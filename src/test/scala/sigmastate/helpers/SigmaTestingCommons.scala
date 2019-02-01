package sigmastate.helpers

import org.ergoplatform.ErgoAddressEncoder.TestnetNetworkPrefix
import org.ergoplatform.{ErgoAddressEncoder, ErgoBox, ErgoLikeContext}
import org.ergoplatform.ErgoBox.{NonMandatoryRegisterId, TokenId}
import org.scalatest.prop.{PropertyChecks, GeneratorDrivenPropertyChecks}
import org.scalatest.{PropSpec, Matchers}
import scorex.crypto.hash.Blake2b256
import scorex.util._
import sigmastate.Values.{Constant, EvaluatedValue, SValue, TrueLeaf, Value, GroupElementConstant}
import sigmastate.eval.{CompiletimeCosting, IRContext, Evaluation}
import sigmastate.interpreter.{CryptoConstants, Interpreter}
import sigmastate.interpreter.Interpreter.{ScriptNameProp, ScriptEnv}
import sigmastate.lang.{TransformingSigmaBuilder, SigmaCompiler}
import sigmastate.{SGroupElement, SBoolean, SType}

import scala.annotation.tailrec
import scala.language.implicitConversions
import scalan.{TestUtils, TestContexts, RType}

trait SigmaTestingCommons extends PropSpec
  with PropertyChecks
  with GeneratorDrivenPropertyChecks
  with Matchers with TestUtils with TestContexts {


  val fakeSelf: ErgoBox = createBox(0, TrueLeaf)

  //fake message, in a real-life a message is to be derived from a spending transaction
  val fakeMessage = Blake2b256("Hello World")

  implicit def grElemConvert(leafConstant: GroupElementConstant): CryptoConstants.EcPointType = leafConstant.value

  implicit def grLeafConvert(elem: CryptoConstants.EcPointType): Value[SGroupElement.type] = GroupElementConstant(elem)

  val compiler = SigmaCompiler(TestnetNetworkPrefix, TransformingSigmaBuilder)

  def compile(env: ScriptEnv, code: String): Value[SType] = {
    compiler.compile(env, code)
  }

  def compileWithCosting(env: ScriptEnv, code: String)(implicit IR: IRContext): Value[SType] = {
    val interProp = compiler.typecheck(env, code)
    val IR.Pair(calcF, _) = IR.doCosting(env, interProp)
    IR.buildTree(calcF)
  }


  def createBox(value: Int,
                proposition: Value[SBoolean.type],
                additionalTokens: Seq[(TokenId, Long)] = Seq(),
                additionalRegisters: Map[NonMandatoryRegisterId, _ <: EvaluatedValue[_ <: SType]] = Map())
    = ErgoBox(value, proposition, 0, additionalTokens, additionalRegisters)

  def createBox(value: Int,
                proposition: Value[SBoolean.type],
                creationHeight: Int)
    = ErgoBox(value, proposition, creationHeight, Seq(), Map(), Array.fill[Byte](32)(0.toByte).toModifierId)

  class TestingIRContext extends TestContext with IRContext with CompiletimeCosting {
    override def onCostingResult[T](env: ScriptEnv, tree: SValue, res: CostingResult[T]): Unit = {
      env.get(ScriptNameProp) match {
        case Some(name: String) =>
          emit(name, res)
        case _ =>
      }
    }
  }

  def func[A:RType,B](func: String)(implicit IR: IRContext): A => B = {
    val tA = RType[A]
    val tpeA = Evaluation.rtypeToSType(tA)
    val code =
      s"""{
        |  val func = $func
        |  val res = func(getVar[${tA.name}](1).get)
        |  res
        |}
      """.stripMargin
    val env = Interpreter.emptyEnv
    val interProp = compiler.typecheck(env, code)
    val IR.Pair(calcF, _) = IR.doCosting(env, interProp)
    val valueFun = IR.compile[SBoolean.type](IR.getDataEnv, IR.asRep[IR.Context => SBoolean.WrappedType](calcF))

    (x: A) => {
      val context = ErgoLikeContext.dummy(createBox(0, TrueLeaf))
          .withBindings(1.toByte -> Constant[SType](x.asInstanceOf[SType#WrappedType], tpeA))
      val calcCtx = context.toSigmaContext(IR, isCost = false)
      val res = valueFun(calcCtx)
      TransformingSigmaBuilder.unliftAny(res).get.asInstanceOf[B]
    }
  }

  def assertExceptionThrown(fun: => Any, assertion: Throwable => Boolean): Unit = {
    try {
      fun
      fail("exception is expected")
    }
    catch {
      case e: Throwable =>
        if (!assertion(e))
          fail(s"exception check failed on $e (caused by: ${e.getCause}")
    }
  }

  @tailrec
  final def rootCause(t: Throwable): Throwable =
    if (t.getCause == null) t
    else rootCause(t.getCause)
}
