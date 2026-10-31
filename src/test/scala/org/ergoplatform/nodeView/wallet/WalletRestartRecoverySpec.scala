package org.ergoplatform.nodeView.wallet

import java.io.File

import akka.actor.{ActorRef, ActorSystem}
import akka.pattern.ask
import akka.util.Timeout
import org.ergoplatform._
import org.ergoplatform.modifiers.mempool.{ErgoTransaction, UnconfirmedTransaction}
import org.ergoplatform.nodeView.ErgoNodeViewHolder.{CurrentView, ReceivableMessages}
import org.ergoplatform.nodeView.ErgoNodeViewRef
import org.ergoplatform.nodeView.mempool.ErgoMemPoolUtils.{ProcessingOutcome, SortingOption}
import org.ergoplatform.nodeView.state.{ErgoState, UtxoState}
import org.ergoplatform.nodeView.wallet.requests.PaymentRequest
import org.ergoplatform.settings.Constants
import org.ergoplatform.settings.Constants.TrueTree
import org.ergoplatform.settings.ErgoSettings
import sigma.Colls
import sigma.ast.ShortConstant
import sigma.interpreter.{ContextExtension, ProverResult}
import org.ergoplatform.utils.{ErgoCorePropertyTest, WalletTestOps}
import org.ergoplatform.utils.fixtures.WalletFixture
import org.ergoplatform.wallet.boxes.ErgoBoxSerializer
import org.scalatest.concurrent.Eventually
import scorex.crypto.authds.ADKey
import scorex.db.{LDBFactory, StoreRegistry}
import scorex.util.bytesToId
import scorex.util.encode.Base16

import scala.concurrent.Await
import scala.concurrent.duration._

class WalletRestartRecoverySpec extends ErgoCorePropertyTest with WalletTestOps with Eventually {
  import org.ergoplatform.utils.ErgoCoreTestConstants._
  import org.ergoplatform.utils.ErgoNodeTestConstants._
  override implicit val patienceConfig: PatienceConfig = PatienceConfig(15.seconds, 100.millis)
  private implicit val addressEncoder: ErgoAddressEncoder =
    ErgoAddressEncoder(ErgoAddressEncoder.TestnetNetworkPrefix)
  private implicit val askTimeout: Timeout = Timeout(20.seconds)

  private type View = CurrentView[ErgoState[_]]

  private def closeStoresUnder(dir: File): Unit = {
    val normalizedRoot = dir.toPath.toAbsolutePath.normalize()
    val registry = LDBFactory.factory.asInstanceOf[StoreRegistry]
    registry.lock.writeLock().lock()
    try {
      val matching = registry.map.toVector.collect {
        case (path, store) if path.toPath.toAbsolutePath.normalize().startsWith(normalizedRoot) =>
          path -> store
      }
      matching.foreach { case (path, store) =>
        store.close()
        registry.map.remove(path)
      }
    } finally registry.lock.writeLock().unlock()
  }

  private def withRestartedView[A](restartedSettings: ErgoSettings, dir: File)
                                  (body: (ActorRef, () => View) => A): A = {
    val restartedSystem = ActorSystem()
    val restarted = ErgoNodeViewRef(restartedSettings)(restartedSystem)
    def fetchView(): View = {
      val request = ReceivableMessages.GetDataFromCurrentView[ErgoState[_], View](v => v)
      Await.result((restarted ? request).mapTo[View], 20.seconds)
    }
    try body(restarted, () => fetchView())
    finally {
      Await.result(restartedSystem.terminate(), 30.seconds)
      closeStoresUnder(dir)
    }
  }

  private def encodeBox(box: ErgoBox): String =
    Base16.encode(ErgoBoxSerializer.toBytes(box))

  private def unsignedLexLess(a: String, b: String): Boolean = {
    val ab = Base16.decode(a).get
    val bb = Base16.decode(b).get
    val len = math.min(ab.length, bb.length)
    var i = 0
    while (i < len) {
      val ai = ab(i) & 0xff
      val bi = bb(i) & 0xff
      if (ai != bi) return ai < bi
      i += 1
    }
    ab.length < bb.length
  }

  private def maxByUnsignedId(txs: Seq[ErgoTransaction]): ErgoTransaction =
    txs.reduceLeft((a, b) => if (unsignedLexLess(a.id, b.id)) b else a)

  property("restore a persisted pending payment into the real mempool after closing and reopening stores") {
    val fixture = new WalletFixture(settings, parameters, getCurrentView(_).vault)
    val pending: ErgoTransaction = try fixture.apply { implicit active =>
      val address = getPublicKeys.head
      applyBlock(makeGenesisBlock(address.pubkey)) shouldBe 'success
      val tx = eventually {
        val amount = getConfirmedBalances.walletBalance / 2
        val fee = math.max(settings.nodeSettings.minimalFeeAmount, 1000000L)
        val requests = Seq(
          PaymentRequest(address, amount, Array.empty, Map.empty),
          PaymentRequest(Pay2SAddress(settings.chainSettings.monetary.feeProposition),
            fee, Array.empty, Map.empty)
        )
        await(wallet.generateTransaction(requests)).get
      }
      wallet.scanOffchain(tx)
      eventually {
        await(wallet.unconfirmedTransactionsToRestore).map(_.id) shouldBe Seq(tx.id)
      }
      getCurrentView.pool.contains(tx.id) shouldBe false
      tx
    } finally {
      Await.result(fixture.actorSystem.whenTerminated, 30.seconds)
      // A wrapper around the same live DB would not establish persistence.
      closeStoresUnder(fixture.nodeViewDir)
    }

    withRestartedView(fixture.settings, fixture.nodeViewDir) { (_, fetchView) =>
      eventually {
        val view = fetchView()
        view.pool.getAll.map(_.id) shouldBe Seq(pending.id)
        Await.result(view.vault.unconfirmedTransactionsToRestore, 20.seconds)
          .map(_.id) shouldBe Seq(pending.id)
      }
    }
  }

  property("retain persisted record when restored transaction is already in the mempool (Declined: AlreadyInPool)") {
    val fixture = new WalletFixture(settings, parameters, getCurrentView(_).vault)
    val pending: ErgoTransaction = try fixture.apply { implicit active =>
      val address = getPublicKeys.head
      applyBlock(makeGenesisBlock(address.pubkey)) shouldBe 'success
      val tx = eventually {
        val amount = getConfirmedBalances.walletBalance / 2
        val fee = math.max(settings.nodeSettings.minimalFeeAmount, 1000000L)
        val requests = Seq(
          PaymentRequest(address, amount, Array.empty, Map.empty),
          PaymentRequest(Pay2SAddress(settings.chainSettings.monetary.feeProposition),
            fee, Array.empty, Map.empty)
        )
        await(wallet.generateTransaction(requests)).get
      }
      wallet.scanOffchain(tx)
      eventually {
        await(wallet.unconfirmedTransactionsToRestore).map(_.id) shouldBe Seq(tx.id)
      }
      tx
    } finally {
      Await.result(fixture.actorSystem.whenTerminated, 30.seconds)
      closeStoresUnder(fixture.nodeViewDir)
    }

    // First restart: once pending is in the pool, a duplicate RestoredTransaction hits
    // Declined(AlreadyInPool) and must not delete the stored wallet record.
    withRestartedView(fixture.settings, fixture.nodeViewDir) { (restarted, fetchView) =>
      val initialView = eventually {
        val v = fetchView()
        v.pool.getAll.map(_.id) shouldBe Seq(pending.id)
        v
      }
      val (_, duplicateOutcome) = initialView.pool.process(UnconfirmedTransaction(pending, None), initialView.state)
      duplicateOutcome shouldBe a[ProcessingOutcome.Declined]
      duplicateOutcome.asInstanceOf[ProcessingOutcome.Declined].reason shouldBe
        ProcessingOutcome.DeclineReason.AlreadyInPool
      duplicateOutcome.retainPersistedWalletTx shouldBe true

      restarted ! ReceivableMessages.RestoredTransaction(UnconfirmedTransaction(pending, None))
      val afterView = fetchView()
      afterView.pool.getAll.map(_.id) shouldBe Seq(pending.id)
      Await.result(afterView.vault.unconfirmedTransactionsToRestore, 20.seconds)
        .map(_.id) shouldBe Seq(pending.id)
    }

    // Second restart into an empty mempool proves the record survived the AlreadyInPool refusal.
    withRestartedView(fixture.settings, fixture.nodeViewDir) { (_, fetchView) =>
      eventually {
        val view = fetchView()
        view.pool.getAll.map(_.id) shouldBe Seq(pending.id)
      }
    }
  }

  property("retain persisted record when mempool refuses restore due to capacity (Declined: PoolCapacity)") {
    val fixture = new WalletFixture(settings, parameters, getCurrentView(_).vault)
    val baseFee = math.max(settings.nodeSettings.minimalFeeAmount, 1000000L)
    val feeProp = settings.chainSettings.monetary.feeProposition
    val feeAddr = Pay2SAddress(feeProp)

    val (lowFeeWalletTx, highFeeNonWalletTx) = try fixture.apply { implicit active =>
      val address = getPublicKeys.head
      applyBlock(makeGenesisBlock(address.pubkey)) shouldBe 'success
      val splitTx = eventually {
        val quarter = getConfirmedBalances.walletBalance / 4
        val requests = Seq(
          PaymentRequest(address, quarter, Array.empty, Map.empty),
          PaymentRequest(Pay2SAddress(TrueTree), quarter, Array.empty, Map.empty),
          PaymentRequest(feeAddr, baseFee, Array.empty, Map.empty)
        )
        await(wallet.generateTransaction(requests)).get
      }
      applyBlock(makeNextBlock(getUtxoState, Seq(splitTx))) shouldBe 'success

      val walletBox = splitTx.outputs.find(_.ergoTree == address.script).get
      val nonWalletBox = splitTx.outputs.find(_.ergoTree == TrueTree).get
      eventually {
        await(wallet.walletBoxes(unspentOnly = true, considerUnconfirmed = false))
          .exists(_.trackedBox.box.id.sameElements(walletBox.id)) shouldBe true
      }

      val walletPayment = await(wallet.generateTransaction(
        requests = Seq(
          PaymentRequest(address, walletBox.value - baseFee, Array.empty, Map.empty),
          PaymentRequest(feeAddr, baseFee, Array.empty, Map.empty)
        ),
        inputsRaw = Seq(encodeBox(walletBox))
      )).get
      wallet.scanOffchain(walletPayment)
      eventually {
        await(wallet.unconfirmedTransactionsToRestore).map(_.id) shouldBe Seq(walletPayment.id)
      }

      val highFee = baseFee * 25
      val externalHighFeeTx = ErgoTransaction(
        IndexedSeq(new Input(nonWalletBox.id, emptyProverResult)),
        IndexedSeq(
          new ErgoBoxCandidate(nonWalletBox.value - highFee, TrueTree, creationHeight = 1),
          new ErgoBoxCandidate(highFee, feeProp, creationHeight = 1)
        )
      )
      (walletPayment, externalHighFeeTx)
    } finally {
      Await.result(fixture.actorSystem.whenTerminated, 30.seconds)
      closeStoresUnder(fixture.nodeViewDir)
    }

    val capOneSettings = fixture.settings.copy(
      nodeSettings = fixture.settings.nodeSettings.copy(
        mempoolCapacity = 1,
        mempoolSorting = SortingOption.FeePerByte
      )
    )

    withRestartedView(capOneSettings, fixture.nodeViewDir) { (restarted, fetchView) =>
      eventually {
        fetchView().pool.contains(lowFeeWalletTx.id) shouldBe true
      }
      val admitHigh = Await.result(
        (restarted ? ReceivableMessages.LocallyGeneratedTransaction(
          UnconfirmedTransaction(highFeeNonWalletTx, None)
        )).mapTo[ProcessingOutcome],
        20.seconds
      )
      admitHigh shouldBe a[ProcessingOutcome.Accepted]

      val fullView = fetchView()
      fullView.pool.getAll.map(_.id) shouldBe Seq(highFeeNonWalletTx.id)
      val (_, capOutcome) = fullView.pool.process(UnconfirmedTransaction(lowFeeWalletTx, None), fullView.state)
      capOutcome shouldBe a[ProcessingOutcome.Declined]
      capOutcome.asInstanceOf[ProcessingOutcome.Declined].reason shouldBe
        ProcessingOutcome.DeclineReason.PoolCapacity
      capOutcome.retainPersistedWalletTx shouldBe true

      restarted ! ReceivableMessages.RestoredTransaction(UnconfirmedTransaction(lowFeeWalletTx, None))
      val afterRefusal = fetchView()
      afterRefusal.pool.getAll.map(_.id) shouldBe Seq(highFeeNonWalletTx.id)
      Await.result(afterRefusal.vault.unconfirmedTransactionsToRestore, 20.seconds)
        .map(_.id) shouldBe Seq(lowFeeWalletTx.id)
    }

    // Reopening with normal capacity restores the retained wallet transaction into the mempool.
    withRestartedView(fixture.settings, fixture.nodeViewDir) { (_, fetchView) =>
      eventually {
        val view = fetchView()
        view.pool.getAll.map(_.id) shouldBe Seq(lowFeeWalletTx.id)
      }
    }
  }

  property("restore dataInput-chained wallet transactions in topological order and retain MissingInputs records") {
    val fixture = new WalletFixture(settings, parameters, getCurrentView(_).vault)
    val baseFee = math.max(settings.nodeSettings.minimalFeeAmount, 1000000L)
    val feeProp = settings.chainSettings.monetary.feeProposition
    val feeAddr = Pay2SAddress(feeProp)

    val (parentTx, dataChildTx, missingInputTx) = try fixture.apply { implicit active =>
      val address = getPublicKeys.head
      applyBlock(makeGenesisBlock(address.pubkey)) shouldBe 'success
      val splitTx = eventually {
        val third = getConfirmedBalances.walletBalance / 3
        val requests = Seq(
          PaymentRequest(address, third, Array.empty, Map.empty),
          PaymentRequest(address, third, Array.empty, Map.empty),
          PaymentRequest(feeAddr, baseFee, Array.empty, Map.empty)
        )
        await(wallet.generateTransaction(requests)).get
      }
      applyBlock(makeNextBlock(getUtxoState, Seq(splitTx))) shouldBe 'success

      val walletBoxes = splitTx.outputs.filter(_.ergoTree == address.script)
      walletBoxes.size should be >= 2
      val box1 = walletBoxes(0)
      val box2 = walletBoxes(1)
      eventually {
        val unspentIds = await(wallet.walletBoxes(unspentOnly = true, considerUnconfirmed = false))
          .map(wb => Base16.encode(wb.trackedBox.box.id)).toSet
        unspentIds.contains(Base16.encode(box1.id)) shouldBe true
        unspentIds.contains(Base16.encode(box2.id)) shouldBe true
      }

      val parent = await(wallet.generateTransaction(
        requests = Seq(
          PaymentRequest(address, box1.value - baseFee, Array.empty, Map.empty),
          PaymentRequest(feeAddr, baseFee, Array.empty, Map.empty)
        ),
        inputsRaw = Seq(encodeBox(box1))
      )).get
      val parentOut = parent.outputs.find(_.ergoTree == address.script).get

      // Pick a child whose txId sorts lexicographically before parent.id in LevelDB so raw DB
      // iteration returns the child first; without dataInputs dependency ordering, validateWithCost
      // would invalidate and delete the child before the parent enters the mempool.
      val candidates = (0L to 64L).map { delta =>
        val fee = baseFee + delta * 1000L
        await(wallet.generateTransaction(
          requests = Seq(
            PaymentRequest(address, box2.value - fee, Array.empty, Map.empty),
            PaymentRequest(feeAddr, fee, Array.empty, Map.empty)
          ),
          inputsRaw = Seq(encodeBox(box2)),
          dataInputsRaw = Seq(encodeBox(parentOut))
        )).get
      }
      val child = candidates.find(c => unsignedLexLess(c.id, parent.id)).getOrElse(candidates.head)
      unsignedLexLess(child.id, parent.id) shouldBe true

      // Also persist an incoming wallet payment spending an external unconfirmed parent box not yet
      // present in UtxoState or mempool, exercising Declined(MissingInputs) on restore.
      val unknownExternalBoxId = ADKey @@ Array.fill[Byte](32)(0x5a.toByte)
      val missingParentChild = ErgoTransaction(
        IndexedSeq(new Input(unknownExternalBoxId, emptyProverResult)),
        IndexedSeq(
          new ErgoBoxCandidate(10000000L, address.script, creationHeight = 1),
          new ErgoBoxCandidate(baseFee, feeProp, creationHeight = 1)
        )
      )

      wallet.scanOffchain(child)
      wallet.scanOffchain(parent)
      wallet.scanOffchain(missingParentChild)
      eventually {
        val toRestore = await(wallet.unconfirmedTransactionsToRestore).map(_.id)
        toRestore.indexOf(parent.id) should be < toRestore.indexOf(child.id)
        toRestore should contain(missingParentChild.id)
      }
      (parent, child, missingParentChild)
    } finally {
      Await.result(fixture.actorSystem.whenTerminated, 30.seconds)
      closeStoresUnder(fixture.nodeViewDir)
    }

    withRestartedView(fixture.settings, fixture.nodeViewDir) { (restarted, fetchView) =>
      val view = eventually {
        val v = fetchView()
        v.pool.getAll.map(_.id).toSet shouldBe Set(parentTx.id, dataChildTx.id)
        v
      }
      val (_, missingOutcome) = view.pool.process(UnconfirmedTransaction(missingInputTx, None), view.state)
      missingOutcome shouldBe a[ProcessingOutcome.Declined]
      missingOutcome.asInstanceOf[ProcessingOutcome.Declined].reason shouldBe
        ProcessingOutcome.DeclineReason.MissingInputs
      missingOutcome.retainPersistedWalletTx shouldBe true

      restarted ! ReceivableMessages.RestoredTransaction(UnconfirmedTransaction(missingInputTx, None))
      val afterMissing = fetchView()
      afterMissing.pool.contains(missingInputTx.id) shouldBe false
      val retainedIds = Await.result(afterMissing.vault.unconfirmedTransactionsToRestore, 20.seconds).map(_.id)
      retainedIds.indexOf(parentTx.id) should be < retainedIds.indexOf(dataChildTx.id)
      retainedIds should contain(missingInputTx.id)
    }
  }

  property("retain child with present regular inputs and unavailable dataInput from a capacity-refused parent, with available-data-box controls") {
    val fixture = new WalletFixture(settings, parameters, getCurrentView(_).vault)
    val baseFee = math.max(settings.nodeSettings.minimalFeeAmount, 1000000L)
    val feeProp = settings.chainSettings.monetary.feeProposition
    val feeAddr = Pay2SAddress(feeProp)

    val (
      blockerTx,
      availableDataValidControlTx,
      parentTx,
      dataChildTx,
      standaloneMissingDataTx,
      availableDataInvalidControlTx
    ) = try fixture.apply { implicit active =>
      val address = getPublicKeys.head
      applyBlock(makeGenesisBlock(address.pubkey)) shouldBe 'success
      val splitTx = eventually {
        val eighth = getConfirmedBalances.walletBalance / 8
        val requests = Seq(
          PaymentRequest(address, eighth, Array.empty, Map.empty),
          PaymentRequest(address, eighth + 1000L, Array.empty, Map.empty),
          PaymentRequest(address, eighth + 2000L, Array.empty, Map.empty),
          PaymentRequest(address, eighth + 3000L, Array.empty, Map.empty),
          PaymentRequest(address, eighth + 4000L, Array.empty, Map.empty),
          PaymentRequest(Pay2SAddress(TrueTree), eighth, Array.empty, Map.empty),
          PaymentRequest(Pay2SAddress(Constants.FalseTree), eighth, Array.empty, Map.empty),
          PaymentRequest(feeAddr, baseFee, Array.empty, Map.empty)
        )
        await(wallet.generateTransaction(requests)).get
      }
      applyBlock(makeNextBlock(getUtxoState, Seq(splitTx))) shouldBe 'success

      val walletBoxes = splitTx.outputs.filter(_.ergoTree == address.script)
      walletBoxes.size should be >= 5
      val box0 = walletBoxes(0)
      val box1 = walletBoxes(1)
      val box2 = walletBoxes(2)
      val box3 = walletBoxes(3)
      val box4 = walletBoxes(4)
      val confirmedDataBox = splitTx.outputs.find(_.ergoTree == TrueTree).get
      val falseScriptBox = splitTx.outputs.find(_.ergoTree == Constants.FalseTree).get

      eventually {
        val unspentIds = await(wallet.walletBoxes(unspentOnly = true, considerUnconfirmed = false))
          .map(wb => Base16.encode(wb.trackedBox.box.id)).toSet
        Seq(box0, box1, box2, box3, box4).foreach { b =>
          unspentIds.contains(Base16.encode(b.id)) shouldBe true
        }
      }

      // Pick a low-fee parent near the top of the unsigned txId space so independent higher-fee
      // transactions sort before it in LevelDB and fill the 2-slot mempool first on startup.
      val parent = maxByUnsignedId((0L until 16L).map { delta =>
        val fee = baseFee + delta * 1000L
        await(wallet.generateTransaction(
          requests = Seq(
            PaymentRequest(address, box1.value - fee, Array.empty, Map.empty),
            PaymentRequest(feeAddr, fee, Array.empty, Map.empty)
          ),
          inputsRaw = Seq(encodeBox(box1))
        )).get
      })
      val parentOut = parent.outputs.find(_.ergoTree == address.script).get

      // Slot-1 filler: independent high-fee transaction with no data inputs.
      val blocker = Iterator.from(0).map { delta =>
        val fee = baseFee * 30 + delta.toLong * 1000L
        await(wallet.generateTransaction(
          requests = Seq(
            PaymentRequest(address, box0.value - fee, Array.empty, Map.empty),
            PaymentRequest(feeAddr, fee, Array.empty, Map.empty)
          ),
          inputsRaw = Seq(encodeBox(box0))
        )).get
      }.find(tx => unsignedLexLess(tx.id, parent.id)).get

      // Slot-2 filler & available-data-box valid control: present regular input box3 plus an
      // available on-chain data box confirmedDataBox.
      val validAvailableDataControl = Iterator.from(0).map { delta =>
        val fee = baseFee * 25 + delta.toLong * 1000L
        await(wallet.generateTransaction(
          requests = Seq(
            PaymentRequest(address, box3.value - fee, Array.empty, Map.empty),
            PaymentRequest(feeAddr, fee, Array.empty, Map.empty)
          ),
          inputsRaw = Seq(encodeBox(box3)),
          dataInputsRaw = Seq(encodeBox(confirmedDataBox))
        )).get
      }.find(tx => unsignedLexLess(tx.id, parent.id)).get

      // Child spends confirmed box2 (present regular input!) and references parentOut ONLY as a
      // dataInput. When parent is refused by PoolCapacity, parentOut is unavailable.
      val childFee = baseFee * 2
      val dataChild = await(wallet.generateTransaction(
        requests = Seq(
          PaymentRequest(address, box2.value - childFee, Array.empty, Map.empty),
          PaymentRequest(feeAddr, childFee, Array.empty, Map.empty)
        ),
        inputsRaw = Seq(encodeBox(box2)),
        dataInputsRaw = Seq(encodeBox(parentOut))
      )).get

      // Standalone transaction with present confirmed regular input box4 and an unavailable
      // external dataInput not produced by any stored parent.
      val unknownExternalDataBox = new ErgoBox(
        10000000L,
        TrueTree,
        Colls.emptyColl,
        Map.empty,
        bytesToId(Array.fill[Byte](32)(0x6b.toByte)),
        0: Short,
        creationHeight = 1
      )
      val standaloneMissingData = await(wallet.generateTransaction(
        requests = Seq(
          PaymentRequest(address, box4.value - childFee, Array.empty, Map.empty),
          PaymentRequest(feeAddr, childFee, Array.empty, Map.empty)
        ),
        inputsRaw = Seq(encodeBox(box4)),
        dataInputsRaw = Seq(encodeBox(unknownExternalDataBox))
      )).get

      // Available-data-box invalid control: both regular input (falseScriptBox) and dataInput
      // (confirmedDataBox) are available on-chain, so the availability precheck passes and
      // validateWithCost rejects it as Invalidated (must be forgotten on restore).
      val invalidControlFee = baseFee * 15
      val invalidAvailableDataControl = ErgoTransaction(
        IndexedSeq(new Input(falseScriptBox.id, emptyProverResult)),
        IndexedSeq(DataInput(confirmedDataBox.id)),
        IndexedSeq(
          new ErgoBoxCandidate(falseScriptBox.value - invalidControlFee, address.script, creationHeight = 1),
          new ErgoBoxCandidate(invalidControlFee, feeProp, creationHeight = 1)
        )
      )

      Seq(
        blocker,
        validAvailableDataControl,
        parent,
        dataChild,
        standaloneMissingData,
        invalidAvailableDataControl
      ).foreach(wallet.scanOffchain)

      eventually {
        val toRestore = await(wallet.unconfirmedTransactionsToRestore).map(_.id)
        toRestore.toSet shouldBe Set(
          blocker.id,
          validAvailableDataControl.id,
          parent.id,
          dataChild.id,
          standaloneMissingData.id,
          invalidAvailableDataControl.id
        )
        toRestore.indexOf(blocker.id) should be < toRestore.indexOf(parent.id)
        toRestore.indexOf(validAvailableDataControl.id) should be < toRestore.indexOf(parent.id)
        toRestore.indexOf(parent.id) should be < toRestore.indexOf(dataChild.id)
      }

      (
        blocker,
        validAvailableDataControl,
        parent,
        dataChild,
        standaloneMissingData,
        invalidAvailableDataControl
      )
    } finally {
      Await.result(fixture.actorSystem.whenTerminated, 30.seconds)
      closeStoresUnder(fixture.nodeViewDir)
    }

    val capTwoSettings = fixture.settings.copy(
      nodeSettings = fixture.settings.nodeSettings.copy(
        mempoolCapacity = 2,
        mempoolSorting = SortingOption.FeePerByte
      )
    )

    // First restart under capacity = 2: blockerTx and availableDataValidControlTx fill the pool;
    // parentTx is refused with PoolCapacity (retained); dataChildTx and standaloneMissingDataTx
    // have present regular inputs but unavailable dataInputs so they get MissingInputs (retained);
    // availableDataInvalidControlTx has both boxes available so it fails validateWithCost as
    // Invalidated and is forgotten.
    withRestartedView(capTwoSettings, fixture.nodeViewDir) { (_, fetchView) =>
      val view = eventually {
        val v = fetchView()
        v.pool.getAll.map(_.id).toSet shouldBe Set(blockerTx.id, availableDataValidControlTx.id)
        val retained = Await.result(v.vault.unconfirmedTransactionsToRestore, 20.seconds).map(_.id).toSet
        retained shouldBe Set(
          blockerTx.id,
          availableDataValidControlTx.id,
          parentTx.id,
          dataChildTx.id,
          standaloneMissingDataTx.id
        )
        v
      }

      val utxo = view.state.asInstanceOf[UtxoState]
      utxo.boxById(dataChildTx.inputs.head.boxId).isDefined shouldBe true
      utxo.boxById(dataChildTx.dataInputs.head.boxId) shouldBe None
      utxo.boxById(standaloneMissingDataTx.inputs.head.boxId).isDefined shouldBe true
      utxo.boxById(standaloneMissingDataTx.dataInputs.head.boxId) shouldBe None
      utxo.boxById(availableDataInvalidControlTx.inputs.head.boxId).isDefined shouldBe true
      utxo.boxById(availableDataInvalidControlTx.dataInputs.head.boxId).isDefined shouldBe true

      val (_, parentOutcome) = view.pool.process(UnconfirmedTransaction(parentTx, None), view.state)
      parentOutcome shouldBe a[ProcessingOutcome.Declined]
      parentOutcome.asInstanceOf[ProcessingOutcome.Declined].reason shouldBe
        ProcessingOutcome.DeclineReason.PoolCapacity
      parentOutcome.retainPersistedWalletTx shouldBe true

      val (_, childOutcome) = view.pool.process(UnconfirmedTransaction(dataChildTx, None), view.state)
      childOutcome shouldBe a[ProcessingOutcome.Declined]
      childOutcome.asInstanceOf[ProcessingOutcome.Declined].reason shouldBe
        ProcessingOutcome.DeclineReason.MissingInputs
      childOutcome.retainPersistedWalletTx shouldBe true
      view.pool.isInvalidated(dataChildTx.id) shouldBe false

      val (_, standaloneOutcome) =
        view.pool.process(UnconfirmedTransaction(standaloneMissingDataTx, None), view.state)
      standaloneOutcome shouldBe a[ProcessingOutcome.Declined]
      standaloneOutcome.asInstanceOf[ProcessingOutcome.Declined].reason shouldBe
        ProcessingOutcome.DeclineReason.MissingInputs
      standaloneOutcome.retainPersistedWalletTx shouldBe true
      view.pool.isInvalidated(standaloneMissingDataTx.id) shouldBe false

      val (_, invalidControlOutcome) =
        view.pool.process(UnconfirmedTransaction(availableDataInvalidControlTx, None), view.state)
      invalidControlOutcome shouldBe a[ProcessingOutcome.Invalidated]
      invalidControlOutcome.retainPersistedWalletTx shouldBe false
      view.pool.isInvalidated(availableDataInvalidControlTx.id) shouldBe true
    }

    // Second restart with normal mempool capacity: parentTx is now admitted and the surviving
    // dataChildTx becomes valid and enters the mempool once parentTx's output is available.
    withRestartedView(fixture.settings, fixture.nodeViewDir) { (_, fetchView) =>
      eventually {
        val view = fetchView()
        view.pool.getAll.map(_.id).toSet shouldBe Set(
          blockerTx.id,
          availableDataValidControlTx.id,
          parentTx.id,
          dataChildTx.id
        )
        val retained = Await.result(view.vault.unconfirmedTransactionsToRestore, 20.seconds).map(_.id).toSet
        retained shouldBe Set(
          blockerTx.id,
          availableDataValidControlTx.id,
          parentTx.id,
          dataChildTx.id,
          standaloneMissingDataTx.id
        )
      }
    }
  }

  property("forget persisted record and unconfirmed descendants on permanent rejection (Invalidated, MinFeeNotMet, MempoolPolicy)") {
    val fixture = new WalletFixture(settings, parameters, getCurrentView(_).vault)
    val baseFee = math.max(settings.nodeSettings.minimalFeeAmount, 1000000L)
    val feeProp = settings.chainSettings.monetary.feeProposition
    val feeAddr = Pay2SAddress(feeProp)

    val (
      address,
      boxAValue,
      blacklistedParentTx,
      childOfBlacklisted,
      dataChildOfBlacklisted,
      underFeeTx,
      storageRentPolicyTx
    ) =
      try fixture.apply { implicit active =>
        val addr = getPublicKeys.head
        applyBlock(makeGenesisBlock(addr.pubkey)) shouldBe 'success
        val splitTx = eventually {
          val fifth = getConfirmedBalances.walletBalance / 5
          val requests = Seq(
            PaymentRequest(addr, fifth, Array.empty, Map.empty),
            PaymentRequest(addr, fifth + 1000L, Array.empty, Map.empty),
            PaymentRequest(addr, fifth + 2000L, Array.empty, Map.empty),
            PaymentRequest(Pay2SAddress(TrueTree), fifth, Array.empty, Map.empty),
            PaymentRequest(feeAddr, baseFee, Array.empty, Map.empty)
          )
          await(wallet.generateTransaction(requests)).get
        }
        applyBlock(makeNextBlock(getUtxoState, Seq(splitTx))) shouldBe 'success

        val walletBoxes = splitTx.outputs.filter(_.ergoTree == addr.script)
        val boxA = walletBoxes(0)
        val boxB = walletBoxes(1)
        val boxC = walletBoxes(2)
        val rentSourceBox = splitTx.outputs.find(_.ergoTree == TrueTree).get
        eventually {
          val unspentIds = await(wallet.walletBoxes(unspentOnly = true, considerUnconfirmed = false))
            .map(wb => Base16.encode(wb.trackedBox.box.id)).toSet
          unspentIds.contains(Base16.encode(boxA.id)) shouldBe true
          unspentIds.contains(Base16.encode(boxB.id)) shouldBe true
          unspentIds.contains(Base16.encode(boxC.id)) shouldBe true
        }

        val parentFee = baseFee * 4
        val blacklistedParent = await(wallet.generateTransaction(
          requests = Seq(
            PaymentRequest(addr, boxA.value - parentFee, Array.empty, Map.empty),
            PaymentRequest(feeAddr, parentFee, Array.empty, Map.empty)
          ),
          inputsRaw = Seq(encodeBox(boxA))
        )).get
        val parentOut = blacklistedParent.outputs.find(_.ergoTree == addr.script).get

        val child = await(wallet.generateTransaction(
          requests = Seq(
            PaymentRequest(addr, parentOut.value - parentFee, Array.empty, Map.empty),
            PaymentRequest(feeAddr, parentFee, Array.empty, Map.empty)
          ),
          inputsRaw = Seq(encodeBox(parentOut))
        )).get

        val dataChild = await(wallet.generateTransaction(
          requests = Seq(
            PaymentRequest(addr, boxC.value - parentFee, Array.empty, Map.empty),
            PaymentRequest(feeAddr, parentFee, Array.empty, Map.empty)
          ),
          inputsRaw = Seq(encodeBox(boxC)),
          dataInputsRaw = Seq(encodeBox(parentOut))
        )).get

        val lowFee = await(wallet.generateTransaction(
          requests = Seq(
            PaymentRequest(addr, boxB.value - baseFee, Array.empty, Map.empty),
            PaymentRequest(feeAddr, baseFee, Array.empty, Map.empty)
          ),
          inputsRaw = Seq(encodeBox(boxB))
        )).get

        val rentClaimInput = new Input(
          rentSourceBox.id,
          ProverResult(
            Array.emptyByteArray,
            ContextExtension(Map(Constants.StorageIndexVarId -> ShortConstant(0)))
          )
        )
        val rentPolicyTx = ErgoTransaction(
          IndexedSeq(rentClaimInput),
          IndexedSeq(
            new ErgoBoxCandidate(rentSourceBox.value - parentFee, addr.script, creationHeight = 1),
            new ErgoBoxCandidate(parentFee, feeProp, creationHeight = 1)
          )
        )

        wallet.scanOffchain(blacklistedParent)
        wallet.scanOffchain(child)
        wallet.scanOffchain(dataChild)
        wallet.scanOffchain(lowFee)
        wallet.scanOffchain(rentPolicyTx)
        eventually {
          await(wallet.unconfirmedTransactionsToRestore).map(_.id).toSet shouldBe
            Set(blacklistedParent.id, child.id, dataChild.id, lowFee.id, rentPolicyTx.id)
        }
        (addr, boxA.value, blacklistedParent, child, dataChild, lowFee, rentPolicyTx)
      } finally {
        Await.result(fixture.actorSystem.whenTerminated, 30.seconds)
        closeStoresUnder(fixture.nodeViewDir)
      }

    val strictSettings = fixture.settings.copy(
      nodeSettings = fixture.settings.nodeSettings.copy(
        blacklistedTransactions = Seq(blacklistedParentTx.id),
        minimalFeeAmount = baseFee * 3,
        rejectStorageRentTxs = true
      )
    )

    withRestartedView(strictSettings, fixture.nodeViewDir) { (_, fetchView) =>
      eventually {
        val view = fetchView()
        view.pool.getAll shouldBe empty

        val (_, policyOutcome) = view.pool.process(
          UnconfirmedTransaction(storageRentPolicyTx, None),
          view.state
        )
        policyOutcome shouldBe a[ProcessingOutcome.Declined]
        policyOutcome.asInstanceOf[ProcessingOutcome.Declined].reason shouldBe
          ProcessingOutcome.DeclineReason.MempoolPolicy
        policyOutcome.retainPersistedWalletTx shouldBe false

        Await.result(view.vault.unconfirmedTransactionsToRestore, 20.seconds) shouldBe empty
        // Once the permanently rejected transactions and dependent child are forgotten, the
        // confirmed on-chain wallet inputs are released in OffChainRegistry and spendable again.
        val replacement = Await.result(
          view.vault.generateTransaction(
            Seq(
              PaymentRequest(address, boxAValue / 2, Array.empty, Map.empty),
              PaymentRequest(feeAddr, baseFee * 3, Array.empty, Map.empty)
            )
          ),
          20.seconds
        )
        replacement.isSuccess shouldBe true
        val newTx = replacement.get
        newTx.id should not be blacklistedParentTx.id
        newTx.id should not be childOfBlacklisted.id
        newTx.id should not be dataChildOfBlacklisted.id
        newTx.id should not be underFeeTx.id
        newTx.id should not be storageRentPolicyTx.id
      }
    }
  }
}
