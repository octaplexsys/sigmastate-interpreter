package sigmastate.utxo.examples

import org.ergoplatform.dsl.{ContractSpec, SigmaContractSyntax, StdContracts, TestContractSpec}
import sigmastate.eval.Extensions
import sigmastate.helpers.SigmaTestingCommons
import special.collection.Coll
import special.sigma.{Box, Context}
import scorex.crypto.hash.Blake2b256

class InterestFreeLoan extends SigmaTestingCommons { suite =>
  implicit lazy val IR = new TestingIRContext

  case class LoanContract[Spec <: ContractSpec]
  (alice: Spec#ProvingParty, bob: Spec#ProvingParty)
  (implicit val spec: Spec) extends SigmaContractSyntax with StdContracts
  {

    /* using the description at https://www.ergoforum.org/t/interest-free-loan-contract/67

   Alice wants to borrow 10000 Euros using Ergs as collateral
   Bob wants to lend 10000 Euros to Alice against installments of 200 Euro per month for 50 months
   (totalling 200*50 = 10000 Euros)

   The amount of collateral is adjusted based on the amount still owed.
   At any time, the collateral must be 1.2 times the value of amount pending to be paid to Bob

   For simplicity, we assume that the loan is paid back by Alice in tokens tethered to Euros.
   These tokens (with tokenID euroToken below) are assumed to be exchangeable by the lender and
   borrower at the rate of 1 token per euro.

   To summarize:
    Loan will be given in actual Euros (with offchain trusted setup)
    Collateral will be in Euros
    Repayment will be in secondary tokens tethered to Euros. This is called equal monthly installments (emi)

    */

    val startRate = 10 // 10 euros per erg
    val rateOracleTokenID:Array[Byte] = Blake2b256("rate".getBytes()).toArray
    val euroTokenID:Array[Byte] = Blake2b256("euro".getBytes()).toArray

    val oneMonth = 720*30 // 720 blocks per day
    val fiveDays = 720*5 // 720 blocks per day
    val emi = 1000 // Euros per month // equal monthly installment

    //val startDate = 10000 // block height at which loan was started

    val miner = alice  // put some other entity here
    val feeProp = miner.pubKey
    val fee = 10
    val feePropBytesHash = blake2b256(feeProp.propBytes)

    lazy val contractEnv = Env(
      "alice" -> alice.pubKey,
      "bob" -> bob.pubKey,
      "fee" -> fee,
      "feeProp" -> feeProp,
      "startRate" -> startRate,
      "oneMonth" -> oneMonth,
      "fiveDays" -> fiveDays,
      "emi" -> emi,
      "rateOracleTokenID" -> rateOracleTokenID,
      "euroTokenID" -> euroTokenID
    )
    lazy val prop = proposition("loanContract", { CONTEXT: Context =>
      import CONTEXT._
      miner.pubKey // dummy line because above doesn't work
    }, """{
        |  val dataInput = CONTEXT.dataInputs(0)
        |  val currentEuros = SELF.R4[Long].get // how many Euros pending
        |  val rate = dataInput.R4[Long].get // rate (how many Euros for 1 ERG)
        |  val correctRateOracle = dataInput.tokens(0)._1 == rateOracleTokenID
        |  val out = OUTPUTS(0) // should be same box script
        |
        |  val lastPaymentHeight = SELF.R5[Int].get // what height last payment was made
        |  val thisPaymentHeight = out.R5[Int].get // what the current height is
        |  val correctHeight = thisPaymentHeight <= HEIGHT && (thisPaymentHeight - lastPaymentHeight > oneMonth)
        |
        |  val correctScript = out.propositionBytes == SELF.propositionBytes
        |
        |  val outEuros = out.R4[Long].get
        |  val euroDiff = currentEuros - outEuros
        |  val ergsDiff = SELF.value - out.value
        |  val correctErgsDiff = euroDiff * rate >= ergsDiff
        |
        |  val correctDiff =  euroDiff == emi && correctErgsDiff
        |
        |  val emiBox = OUTPUTS(1) // this is the box where Alice will pay to Bob
        |  val correctEmiAmt = emiBox.tokens(0)._1 == euroTokenID && emiBox.tokens(0)._2 >= emi
        |  val correctEmiScript = emiBox.propositionBytes == proveDlog(bob).propBytes
        |  val correctEmi = correctEmiAmt && correctEmiScript
        |
        |  val nonPayment = (HEIGHT - lastPaymentHeight) > (oneMonth + fiveDays)
        |
        |  // todo add more logic (profit sharing by Alice and Bob when Euro price drops)
        |  val correctTx = correctDiff && correctScript && correctRateOracle && correctHeight
        |
        |  correctTx && ((proveDlog(alice) && correctEmi) || (proveDlog(bob) && nonPayment))
        |
        |}""".stripMargin)

    lazy val requireAliceSignature =  proposition(
      "requireAliceSignature",
      _ => alice.pubKey,
      "alice"
    )
    lazy val requireBobSignature =  proposition(
      "requireBobSignature",
      _ => bob.pubKey,
      "bob"
    )
    lazy val requireMinerSignature =  proposition(
      "feeProp", _ => miner.pubKey, "feeProp"
    )

  }

  lazy val spec = TestContractSpec(suite)(new TestingIRContext)

  lazy val alice = spec.ProvingParty("Alice")
  lazy val bob = spec.ProvingParty("Bob")

  property("Loan contract") {
    val contract = LoanContract[spec.type](alice, bob)(spec)

    import contract.spec._

    val mockTx = candidateBlock(0).newTransaction()

    val deposit = mockTx.outBox(110, contract.prop)

    val tx = candidateBlock(10).newTransaction().spending(deposit)

    tx.outBox(50, contract.requireAliceSignature)
    tx.outBox(30, contract.requireBobSignature)
    tx.outBox(10, contract.requireMinerSignature)

    val in = tx.inputs(0)

    val res = in.runDsl(Map(1.toByte -> Extensions.toAnyValue(1)))

    val pr = alice.prove(in).get
    contract.verifier.verify(in, pr) shouldBe true
  }
}

