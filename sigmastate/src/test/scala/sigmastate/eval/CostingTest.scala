package sigmastate.eval

import java.math.BigInteger

import com.google.common.base.Strings
import org.bouncycastle.math.ec.ECPoint
import sigmastate._
import sigmastate.Values.{ConstantPlaceholder, _}
import sigmastate.helpers.ContextEnrichingTestProvingInterpreter
import sigmastate.interpreter.CryptoConstants
import sigmastate.lang.{LangTests, TransformingSigmaBuilder, SigmaCompiler}
import sigmastate.utxo.CostTable.Cost
import sigmastate.utxo.{SigmaPropBytes, ExtractCreationInfo, SizeOf, SelectField}
import SType._
import org.ergoplatform.{Height, Self, MinerPubkey}
import scalan.util.BenchmarkUtil._
import scalan.BaseCtxTests
import sigmastate.SCollection.SByteArray
import sigmastate.basics.DLogProtocol
import sigmastate.basics.DLogProtocol.ProveDlog
import sigmastate.lang.Terms.ValueOps
import sigmastate.serialization.OpCodes

class CostingTest extends BaseCtxTests with LangTests with ExampleContracts with ErgoScriptTestkit { cake =>
  implicit override lazy val IR: TestContext with IRContext =
    new TestContext with IRContext with CompiletimeCosting {
    }
  import IR._
  import GroupElement._
  import BigInt._
  import Context._; import SigmaContract._
  import Cost._; import CollBuilder._; import Coll._; import Box._; import SigmaProp._;
  import SigmaDslBuilder._; import WOption._
  import Liftables._
  
  ignore("SType.dataSize") {
    def check(tpe: SType, v: Any, exp: Long) =
      tpe.dataSize(v.asWrappedType) shouldBe exp

    check(SBoolean, true, 1)
    check(SByte, 1.toByte, 1)
    check(SShort, 1.toShort, 2)
    check(SInt, 1, 4)
    check(SLong, 1, 8)
    check(SString, "abc", 3)
    check(SBigInt, BigInteger.ZERO, SBigInt.MaxSizeInBytes)
    check(SBigInt, BigInteger.ONE, SBigInt.MaxSizeInBytes)
    check(SBigInt, BigInteger.valueOf(Long.MaxValue), SBigInt.MaxSizeInBytes)
    check(SBigInt, { val i = BigInteger.valueOf(Long.MaxValue); i.multiply(i) }, SBigInt.MaxSizeInBytes)
    val g = CryptoConstants.dlogGroup.generator
    check(SGroupElement, g, CryptoConstants.groupSize)
    check(SSigmaProp, DLogProtocol.ProveDlog(g), CryptoConstants.groupSize + 1)
    check(sigmastate.SOption(SInt), Some(10), 1 + 4)
    def checkColl(elemTpe: SType, arr: Array[Any], exp: Long) =
      check(sigmastate.SCollection(SInt), arr, exp)
    checkColl(SInt, Array(10,20), 2 + 2L * 4)
    checkColl(SInt, Array(), 2)
    checkColl(SBigInt, Array(BigInteger.ZERO, BigInteger.valueOf(Long.MaxValue)), 2 + 0 + 8)
    check(STuple(SInt, STuple(SInt, SInt)), Array(10, Array[Any](20, 30)), 2 + 4 + (2 + 4 + 4))
  }

  ignore("constants") {
//    check("int", "1", _ => 1, _ => constCost[Int], _ => sizeOf(1))
//    check("long", "1L", _ => 1L, _ => constCost[Long], _ => sizeOf(1L))
//    check("boolean", "true", _ => true, _ => constCost[Boolean], _ => sizeOf(true))
//    checkInEnv(env, "byte", "b1", _ => 1.toByte, _ => constCost[Byte], _ => sizeOf(1.toByte))
//
    val arr1 = env("arr1").asInstanceOf[Array[Byte]]
    val symArr1 = liftConst(Colls.fromArray(arr1))
    checkInEnv(env, "arr", "arr1",
      {_ => symArr1},
      {_ => constCost[Coll[Byte]]})
    checkInEnv(env, "arr2", "arr1.size",
      {_ => liftConst(Colls.fromArray(arr1)).length },
      { _ =>
        val c = ByteArrayConstant(arr1)
        costOf(c) + costOf(utxo.SizeOf(c))
      })

    val n1Sym = liftConst(n1)
    checkInEnv(env, "bigint", "n1", {_ => n1Sym }, { _ => constCost[BigInt] })

    val g1Sym = liftConst(g1)
    checkInEnv(env, "group", "g1", {_ => g1Sym }, {_ => constCost[GroupElement]})

    checkInEnv(env, "sigmaprop", "p1.propBytes",
      { _ => liftConst(dslValue.SigmaProp(p1)).propBytes }
    )
  }

  ignore("operations") {
    import NumericOps._
    import builder._
    check("one+one", "1 + 1", _ => toRep(1) + 1,
      {_ => val c1 = IntConstant(1); costOf(c1) + costOf(c1) + costOf(Plus(c1, c1)) })
    checkInEnv(env, "one+one2", "big - n1", {_ => liftConst(dslValue.BigInt(big)).subtract(liftConst(n1))})
    check("one_gt_one", "1 > 1", {_ => toRep(1) > 1},
      { _ =>
        val c1 = IntConstant(1);
        costOf(c1) + costOf(c1) + costOf(GT(c1,c1))
      })
//    checkInEnv(env, "or", "1 > 1 || n1 < big", {_ => (toRep(1) > 1) lazy_|| Thunk(toRep(n1) < big)},
//      { _ =>
//        val (lv, lc) = {
//          val c1 = IntConstant(1);
//          val res = mkGT(c1, c1); (res, costOf(c1) + costOf(c1) + costOf(res)) }
//        val (rv, rc) = {
//          val c1 = BigIntConstant(n1);
//          val c2 = BigIntConstant(big);
//          val res = mkLT(c1, c1); (res, costOf(c1) + costOf(c2) + costOf(res)) }
//        lc + rc + costOf(mkBinOr(lv, rv))
//      })
//    check("or2", "1 > 1 || 2 < 1 || 2 > 1", _ => true,
//      _ => ConstantNode * 6 + TripleDeclaration * 3 + 2 * BinOrDeclaration)
//    check("or3", "OUTPUTS.size > 1 || OUTPUTS.size < 1",
//      { ctx => (ctx.OUTPUTS.length > 1) lazy_|| Thunk(ctx.OUTPUTS.length < 1)  },
//      _ => (OutputsAccess + SizeOfDeclaration) * 2 + TripleDeclaration * 2 + ConstantNode * 2 + BinOrDeclaration)
//
//    check("and", "1 > 1 && 2 < 1", _ => false, _ => ConstantNode * 4 + TripleDeclaration * 2 + BinAndDeclaration)
//    check("and2", "1 > 1 && 2 < 1 && 2 > 1", _ => false,
//      _ => ConstantNode * 6 + TripleDeclaration * 3 + 2 * BinAndDeclaration)
//    check("and3", "OUTPUTS.size > 1 && OUTPUTS.size < 1",
//      { ctx => (ctx.OUTPUTS.length > 1) lazy_&& Thunk(ctx.OUTPUTS.length < 1) },
//      _ => (OutputsAccess + SizeOfDeclaration) * 2 + TripleDeclaration * 2 + ConstantNode * 2 + BinAndDeclaration)
  }

  test("context data") {
//    check("var1", "getVar[BigInt](1)", ctx => ctx.getVar[BigInteger](1.toByte), _ => 1)
    def plus[T: Elem](x: Ref[T], y: Ref[T]) = ApplyBinOp(opcodeToEndoBinOp(OpCodes.PlusCode, element[T]), x, y)
    check("height1", "HEIGHT + 1", ctx => plus(ctx.HEIGHT, 1))
    check("height2", "HEIGHT > 1", ctx => ctx.HEIGHT > 1)
    check("size", "INPUTS.size + OUTPUTS.size", ctx => { plus(ctx.INPUTS.length, ctx.OUTPUTS.length) })
    check("value", "SELF.value + 1L", ctx => plus(ctx.SELF.value, 1L))
  }

  test("collection ops") {
    check("exists", "OUTPUTS.exists { (out: Box) => out.value >= 0L }",
      ctx => ctx.OUTPUTS.exists(fun(out => { out.value >= 0L })))
    check("forall", "OUTPUTS.forall { (out: Box) => out.value >= 0L }",
      ctx => ctx.OUTPUTS.forall(fun(out => { out.value >= 0L })))
    check("map", "OUTPUTS.map { (out: Box) => out.value >= 0L }",
      ctx => ctx.OUTPUTS.map(fun(out => { out.value >= 0L })))
//    check("where", "OUTPUTS.where(fun (out: Box) = { out.value >= 0L })",
//      ctx => ctx.OUTPUTS.filter(fun(out => { out.value >= 0L })))
  }

  ignore("lambdas") {
    check("lam1", "{ (out: Box) => out.value >= 0L }",
      ctx => fun { out: Ref[Box] => out.value >= 0L }, null, {_ => 8L})
    check("lam2", "{ val f = { (out: Box) => out.value >= 0L }; f }",
      ctx => fun { out: Ref[Box] => out.value >= 0L }, null, {_ => 8L})
    check("lam3", "{ val f = { (out: Box) => out.value >= 0L }; f(SELF) }",
      ctx => { val f = fun { out: Ref[Box] => out.value >= 0L }; Apply(f, ctx.SELF, false) })
    check("lam4", "{ def f(out: Box) = out.value >= 0L ; f }",
      ctx => fun { out: Ref[Box] => out.value >= 0L }, null, {_ => 8L})
  }

  test("if then else") {
    check("lam1", "{ val x = if (OUTPUTS.size > 0) OUTPUTS(0).value else SELF.value; x }",
      { ctx => val x = IF (ctx.OUTPUTS.length > 0) THEN ctx.OUTPUTS(0).value ELSE ctx.SELF.value; x })
  }

  ignore("Crowd Funding") {
    val prover = new ContextEnrichingTestProvingInterpreter()
    val backerPK  = prover.dlogSecrets(0).publicImage
    val projectPK = prover.dlogSecrets(1).publicImage

    val env = envCF ++ Seq("projectPubKey" -> projectPK, "backerPubKey" -> backerPK)
    checkInEnv(env, "CrowdFunding", crowdFundingScript,
      { ctx: Ref[Context] =>
        val backerPubKey = liftConst(dslValue.SigmaProp(backerPK))
        val projectPubKey = liftConst(dslValue.SigmaProp(projectPK))
        val projectBytes = projectPubKey.propBytes
        val c1 = asRep[SigmaProp](dsl.sigmaProp(ctx.HEIGHT >= toRep(timeout))) && backerPubKey
        val c2 = asRep[SigmaProp](dsl.sigmaProp(dsl.allOf(colBuilder.fromItems(
          ctx.HEIGHT < toRep(timeout),
          ctx.OUTPUTS.exists(fun { out =>
            out.value >= toRep(minToRaise) lazy_&& Thunk(out.propositionBytes === projectBytes)
          }))
        ))) && projectPubKey
        (c1 || c2)
      }
      )
  }

  test("Crowd Funding: measure") {
    val prover = new ContextEnrichingTestProvingInterpreter()
    val backerPK  @ DLogProtocol.ProveDlog(backer: ECPoint) = prover.dlogSecrets(0).publicImage
    val projectPK @ DLogProtocol.ProveDlog(project: ECPoint) = prover.dlogSecrets(1).publicImage
    val env = envCF ++ Seq("projectPubKey" -> projectPK, "backerPubKey" -> backerPK)
    val parsed = compiler.parse(crowdFundingScript)
    val env2 = env ++ Seq("timeout" -> (timeout + 1))
    val typed = compiler.typecheck(env2, parsed)
    def eval(i: Int) = {
      val cf = cost(env2, typed)
      cf
    }

    println("Warming up ...")
    var res: Ref[Any] = null
    for (i <- 1 to 1000)
      res = eval(i)

    println("Processing ...")
    measure(3) { k =>
      for (i <- 1 to 1000)
        res = eval(i)
    }
    
    emit("Crowd_Funding_measure", res)
    /*
    Warming up ...
    Processing ...
    Iter 0: 2138 ms
    Iter 1: 1864 ms
    Iter 2: 1864 ms
    Total time: 5866 ms
    */
  }

  test("Demurrage") {
    val prover = new ContextEnrichingTestProvingInterpreter()
    val regScriptPK = prover.dlogSecrets(0).publicImage
    val env = envDem ++ Seq("regScript" -> regScriptPK)
    checkInEnv(env, "Demurrage", demurrageScript, null)
  }

  test("measure: costed context data") {
    var res: Ref[Any] = null
    measure(2) { j => // 10 warm up iterations when j == 0
      measure(j*1000 + 10, false) { i =>
        res = check("", s"INPUTS.size + OUTPUTS.size + $i", null
          /*ctx => ctx.INPUTS.length + ctx.OUTPUTS.length + i*/, printGraphs = false)
      }
    }
    emit("costed_context_data", res)
    /*
    Total time: 2676 ms
    Iter 0: 2676 ms
    Total time: 6966 ms
    Iter 1: 6970 ms
    Total time: 9646 ms
    */
  }


}
