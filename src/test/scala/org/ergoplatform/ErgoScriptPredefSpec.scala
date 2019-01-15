package org.ergoplatform

import org.ergoplatform.ErgoBox.R4
import org.ergoplatform.mining.emission.EmissionRules
import org.ergoplatform.settings.MonetarySettings
import org.scalacheck.Gen
import scorex.crypto.hash.{Blake2b256, Digest32}
import sigmastate.Values.{ByteArrayConstant, IntConstant, LongConstant, Value}
import sigmastate.basics.DLogProtocol.ProveDlog
import sigmastate.helpers.{ErgoLikeTestProvingInterpreter, SigmaTestingCommons}
import sigmastate.interpreter.Interpreter.{ScriptNameProp, emptyEnv}
import sigmastate.interpreter.{ContextExtension, ProverResult}
import sigmastate.lang.Terms.ValueOps
import sigmastate.serialization.ValueSerializer
import sigmastate.utxo.{ByIndex, ErgoLikeTestInterpreter, ExtractCreationInfo, SelectField}
import sigmastate.{AvlTreeData, EQ, SBoolean, Values}

import scala.util.Try

class ErgoScriptPredefSpec extends SigmaTestingCommons {
  implicit lazy val IR = new TestingIRContext {
    override val okPrintEvaluatedEntries: Boolean = false
  }
  val emptyProverResult: ProverResult = ProverResult(Array.emptyByteArray, ContextExtension.empty)
  private val settings = MonetarySettings(30 * 2 * 24 * 365, 90 * 24 * 30, 75L * EmissionRules.CoinsInOneErgo,
    3L * EmissionRules.CoinsInOneErgo, 720, 75L * EmissionRules.CoinsInOneErgo / 10, "")
  private val emission = new EmissionRules(settings)


  ignore("boxCreationHeight") {
    val verifier = new ErgoLikeTestInterpreter
    val prover = new ErgoLikeTestProvingInterpreter
    val minerProp = prover.dlogSecrets.head.publicImage
    val pk = minerProp.pkBytes

    val nextHeight = 1
    val prop = EQ(Height, ErgoScriptPredef.boxCreationHeight(ByIndex(Outputs, IntConstant(0))))
    val propInlined = EQ(Height, SelectField(ExtractCreationInfo(ByIndex(Outputs, IntConstant(0))), 1).asIntValue)
    prop shouldBe propInlined
    val inputBox = ErgoBox(1, prop, nextHeight, Seq(), Map())
    val inputBoxes = IndexedSeq(inputBox)
    val inputs = inputBoxes.map(b => Input(b.id, emptyProverResult))
    val minerBox = new ErgoBoxCandidate(1, minerProp, nextHeight, Seq(), Map())

    val spendingTransaction = ErgoLikeTransaction(inputs, IndexedSeq(minerBox))

    val ctx = ErgoLikeContext(
      currentHeight = nextHeight,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      minerPubkey = pk,
      boxesToSpend = inputBoxes,
      spendingTransaction,
      self = inputBox)
    val pr = prover.prove(emptyEnv + (ScriptNameProp -> "prove"), prop, ctx, fakeMessage).get
    verifier.verify(emptyEnv + (ScriptNameProp -> "verify"), prop, ctx, pr, fakeMessage).get._1 shouldBe true
  }

  property("collect coins from founders box") {
    def remaining(h: Int) = emission.remainingFoundationRewardAtHeight(h)

    val foundersCoinsTotal = remaining(0)
    val prover = new ErgoLikeTestProvingInterpreter
    val prop = ErgoScriptPredef.foundationScript(settings.fixedRatePeriod, settings.epochLength,
      settings.oneEpochReduction, settings.foundersInitialReward)

    val verifier = new ErgoLikeTestInterpreter

    checkAtHeight(1)
    checkAtHeight(settings.fixedRatePeriod)
    checkAtHeight(settings.fixedRatePeriod + 1)
    checkAtHeight(settings.fixedRatePeriod + settings.epochLength)
    checkAtHeight(settings.fixedRatePeriod + settings.epochLength + 1)
    checkAtHeight(settings.fixedRatePeriod + 2 * settings.epochLength)
    checkAtHeight(settings.fixedRatePeriod + 2 * settings.epochLength + 1)

    def checkAtHeight(height: Int) = {
      checkSpending(remaining(height), height, prop) shouldBe 'success
      checkSpending(remaining(height), height, Values.TrueLeaf) shouldBe 'failure
      checkSpending(remaining(height) + 1, height, prop) shouldBe 'success
      checkSpending(remaining(height) - 1, height, prop) shouldBe 'failure
    }

    def checkSpending(remainingAmount: Long, height: Int, newProp: Value[SBoolean.type]): Try[Unit] = Try {
      val serializedR4Val = ByteArrayConstant(ValueSerializer.serialize(Values.TrueLeaf))
      val inputBoxes = IndexedSeq(ErgoBox(foundersCoinsTotal, prop, 0, Seq(), Map(R4 -> serializedR4Val)))
      val inputs = inputBoxes.map(b => Input(b.id, emptyProverResult))
      val newFoundersBox = ErgoBox(remainingAmount, newProp, 0)
      val collectedBox = ErgoBox(inputBoxes.head.value - remainingAmount, Values.TrueLeaf, 0)
      val spendingTransaction = ErgoLikeTransaction(inputs, IndexedSeq(newFoundersBox, collectedBox))
      val ctx = ErgoLikeContext(
        currentHeight = height,
        lastBlockUtxoRoot = AvlTreeData.dummy,
        minerPubkey = ErgoLikeContext.dummyPubkey,
        boxesToSpend = inputBoxes,
        spendingTransaction,
        self = inputBoxes.head)
      val pr = prover.prove(emptyEnv + (ScriptNameProp -> "prove"), prop, ctx, fakeMessage).get
      verifier.verify(emptyEnv + (ScriptNameProp -> "verify"), prop, ctx, pr, fakeMessage).get._1 shouldBe true
    }

  }

  property("collect coins from rewardOutputScript") {
    val prover = new ErgoLikeTestProvingInterpreter
    val minerPk = prover.dlogSecrets.head.publicImage
    val prop = ErgoScriptPredef.rewardOutputScript(settings.minerRewardDelay, minerPk)
    val verifier = new ErgoLikeTestInterpreter
    val inputBoxes = IndexedSeq(ErgoBox(20, prop, 0, Seq(), Map()))
    val inputs = inputBoxes.map(b => Input(b.id, emptyProverResult))
    val spendingTransaction = ErgoLikeTransaction(inputs, IndexedSeq(ErgoBox(inputBoxes.head.value, Values.TrueLeaf, 0)))

    val ctx = ErgoLikeContext(
      currentHeight = inputBoxes.head.creationHeight + settings.minerRewardDelay,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      minerPubkey = ErgoLikeContext.dummyPubkey,
      boxesToSpend = inputBoxes,
      spendingTransaction,
      self = inputBoxes.head)
    val prevBlockCtx = ErgoLikeContext(
      currentHeight = inputBoxes.head.creationHeight + settings.minerRewardDelay - 1,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      minerPubkey = ErgoLikeContext.dummyPubkey,
      boxesToSpend = inputBoxes,
      spendingTransaction,
      self = inputBoxes.head)

    // should not be able to collect before minerRewardDelay
    val prove = prover.prove(emptyEnv + (ScriptNameProp -> "prove"), prop, ctx, fakeMessage).get
    verifier.verify(emptyEnv + (ScriptNameProp -> "verify"), prop, prevBlockCtx, prove, fakeMessage) shouldBe 'failure

    // should be able to collect after minerRewardDelay
    val pr = prover.prove(emptyEnv + (ScriptNameProp -> "prove"), prop, ctx, fakeMessage).get
    verifier.verify(emptyEnv + (ScriptNameProp -> "verify"), prop, ctx, pr, fakeMessage).get._1 shouldBe true
  }

  property("create transaction collecting the result") {
    val prover = new ErgoLikeTestProvingInterpreter
    val minerPk = prover.dlogSecrets.head.publicImage
    val prop = ErgoScriptPredef.emissionBoxProp(settings.fixedRatePeriod, settings.epochLength, settings.fixedRate,
      settings.oneEpochReduction, settings.minerRewardDelay)
    val emissionBox = ErgoBox(emission.coinsTotal, prop, 0, Seq(), Map(ErgoBox.nonMandatoryRegisters.head -> LongConstant(-1)))
    val minerProp = ErgoScriptPredef.rewardOutputScript(settings.minerRewardDelay, minerPk)

    // collect coins during the fixed rate period
    forAll(Gen.choose(1, settings.fixedRatePeriod)) { height =>
      createRewardTx(settings.fixedRate, height, minerProp) shouldBe 'success
      createRewardTx(settings.fixedRate + 1, height, minerProp) shouldBe 'failure
      createRewardTx(settings.fixedRate - 1, height, minerProp) shouldBe 'failure
    }

    // collect coins after the fixed rate period
    forAll(Gen.choose(1, emission.blocksTotal - 1)) { height =>
      val currentRate = emission.emissionAtHeight(height)
      createRewardTx(currentRate, height, minerProp) shouldBe 'success
      createRewardTx(currentRate + 1, height, minerProp) shouldBe 'failure
      createRewardTx(currentRate - 1, height, minerProp) shouldBe 'failure
    }

    // collect coins to incorrect proposition
    forAll(Gen.choose(1, emission.blocksTotal - 1)) { height =>
      val currentRate = emission.emissionAtHeight(height)
      val minerProp2 = ErgoScriptPredef.rewardOutputScript(settings.minerRewardDelay + 1, minerPk)
      createRewardTx(currentRate, height, minerProp2) shouldBe 'failure
      createRewardTx(currentRate, height, minerPk) shouldBe 'failure
    }

    def createRewardTx(emissionAmount: Long, nextHeight: Int, minerProp: Value[SBoolean.type]): Try[ErgoLikeTransaction] = {
      checkRewardTx(minerPk: ProveDlog,
        minerProp: Value[SBoolean.type],
        emissionBox: ErgoBox,
        emissionAmount: Long,
        nextHeight: Int)(prover)
    }

  }

  property("tokenThreshold") {
    val prover = new ErgoLikeTestProvingInterpreter
    val verifier = new ErgoLikeTestInterpreter

    val pubkey = prover.dlogSecrets.head.publicImage

    val tokenId: Digest32 = Blake2b256("id")
    val wrongId: Digest32 = Blake2b256(tokenId)
    val wrongId2: Digest32 = Blake2b256(wrongId)
    val tokenAmount: Int = 50

    val prop = ErgoScriptPredef.tokenThresholdScript(tokenId, tokenAmount)

    def check(inputBoxes: IndexedSeq[ErgoBox]): Try[Unit] = Try {
      val inputs = inputBoxes.map(b => Input(b.id, emptyProverResult))
      val amount = inputBoxes.map(_.value).sum
      val spendingTransaction = ErgoLikeTransaction(inputs, IndexedSeq(ErgoBox(amount, pubkey, 0)))

      val ctx = ErgoLikeContext(
        currentHeight = 50,
        lastBlockUtxoRoot = AvlTreeData.dummy,
        minerPubkey = ErgoLikeContext.dummyPubkey,
        boxesToSpend = inputBoxes,
        spendingTransaction,
        self = inputBoxes.head)

      val pr = prover.prove(emptyEnv + (ScriptNameProp -> "prove"), prop, ctx, fakeMessage).get
      verifier.verify(emptyEnv + (ScriptNameProp -> "verify"), prop, ctx, pr, fakeMessage).get._1 shouldBe true
    }


    // transaction with the only input with enough token should pass
    val inputs0 = IndexedSeq(
      ErgoBox(20, prop, 0, Seq((wrongId, tokenAmount), (tokenId, tokenAmount), (wrongId2, tokenAmount)), Map())
    )
    check(inputs0) shouldBe 'success

    // transaction with the only input with insufficient token should fail
    val inputs1 = IndexedSeq(
      ErgoBox(20, prop, 0, Seq((wrongId, tokenAmount), (tokenId, tokenAmount - 1)), Map())
    )
    check(inputs1) shouldBe 'failure

    // transaction with multiple inputs with insufficient token should fail
    val inputs2 = IndexedSeq(
      ErgoBox(20, prop, 0, Seq((wrongId, tokenAmount), (tokenId, tokenAmount - 2)), Map()),
      ErgoBox(20, prop, 0, Seq((wrongId, tokenAmount)), Map()),
      ErgoBox(20, prop, 0, Seq((tokenId, 1), (wrongId2, tokenAmount)), Map())
    )
    check(inputs2) shouldBe 'failure

    // transaction with multiple inputs with enough token should pass
    val inputs3 = IndexedSeq(
      ErgoBox(20, prop, 0, Seq((wrongId, 1), (tokenId, tokenAmount / 2)), Map()),
      ErgoBox(20, prop, 0, Seq((wrongId, 1)), Map()),
      ErgoBox(20, prop, 0, Seq((tokenId, tokenAmount / 2 + 1), (wrongId2, 1)), Map())
    )
    check(inputs3) shouldBe 'success

  }

  def checkRewardTx(minerPk: ProveDlog,
                    minerProp: Value[SBoolean.type],
                    emissionBox: ErgoBox,
                    emissionAmount: Long,
                    nextHeight: Int)(prover: ErgoLikeTestProvingInterpreter): Try[ErgoLikeTransaction] = Try {
    val verifier = new ErgoLikeTestInterpreter
    val prop = emissionBox.proposition
    val inputBoxes = IndexedSeq(emissionBox)
    val inputs = inputBoxes.map(b => Input(b.id, emptyProverResult))
    val pkBytes = minerPk.pkBytes

    val newEmissionBox: ErgoBoxCandidate = new ErgoBoxCandidate(emissionBox.value - emissionAmount, prop,
      nextHeight, Seq(), Map())
    val minerBox = new ErgoBoxCandidate(emissionAmount, minerProp, nextHeight, Seq(), Map())

    val spendingTransaction = ErgoLikeTransaction(inputs, IndexedSeq(newEmissionBox, minerBox))

    val ctx = ErgoLikeContext(
      currentHeight = nextHeight,
      lastBlockUtxoRoot = AvlTreeData.dummy,
      minerPubkey = pkBytes,
      boxesToSpend = inputBoxes,
      spendingTransaction,
      self = inputBoxes.head)
    val pr = prover.prove(emptyEnv + (ScriptNameProp -> "prove"), prop, ctx, fakeMessage).get
    verifier.verify(emptyEnv + (ScriptNameProp -> "verify"), prop, ctx, pr, fakeMessage).get._1 shouldBe true
    spendingTransaction
  }

}
