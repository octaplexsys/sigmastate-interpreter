package sigmastate.eval

import java.math.BigInteger

import org.bouncycastle.math.ec.ECPoint
import org.ergoplatform._
import sigmastate.SCollection.SByteArray
import sigmastate._
import sigmastate.Values.{BigIntArrayConstant, BigIntConstant, ByteArrayConstant, FalseLeaf, GroupElementConstant, IntConstant, LongConstant, SigmaBoolean, SigmaPropConstant, TrueLeaf, ValUse}
import sigmastate.helpers.ErgoLikeTestProvingInterpreter
import sigmastate.interpreter.{ContextExtension, CryptoConstants}
import sigmastate.lang.DefaultSigmaBuilder.mkTaggedVariable
import sigmastate.lang.LangTests
import sigmastate.utxo._
import special.collection.{Coll => VColl}
import special.sigma.{TestValue => VTestValue}
import scalan.BaseCtxTests
import scalan.util.BenchmarkUtil._
import sigmastate.basics.DLogProtocol
import special.sigma._

class CompilerItTest extends BaseCtxTests
    with LangTests with ExampleContracts with ErgoScriptTestkit {
  import IR._
  import builder._
  import WArray._
  import WOption._
  import CollBuilder._
  import SigmaDslBuilder._
  import Context._
  import Coll._
  import SigmaProp._
  import CostedColl._
  import CCostedColl._
  import WBigInteger._
  import WECPoint._
  import BigInt._
  import GroupElement._
  import sigmastate.serialization.OpCodes._
  import Liftables._
  import SType.AnyOps


  def intConstCase = {
    Case(env, "intConst", "1", ergoCtx,
      calc = {_ => 1 },
      cost = {_ => constCost[Int]},
      size = {_ => sizeOf(1)},
      tree = IntConstant(1), Result(1, 1, 4))
  }
  test("intConstCase") {
    intConstCase.doReduce
  }

  def bigIntegerConstCase = {
    Case(env, "bigIntegerConst", "big", ergoCtx,
      calc = {_ => bigSym },
      cost = {_ => constCost[BigInt]},
      size = {_ => SBigInt.MaxSizeInBytes },
      tree = BigIntConstant(big), Result(big, 1, 32))
  }
  test("bigIntegerConstCase") {
    bigIntegerConstCase.doReduce
  }

  def addBigIntegerConstsCase = {
//    val size = (sizeOf(bigSym) max sizeOf(n1Sym)) + 1L
    val res = big.add(n1)
    Case(env, "addBigIntegerConsts", "big + n1", ergoCtx,
      calc = {_ => bigSym.add(n1Sym) },
      cost = {_ => constCost[BigInt] + constCost[BigInt] +
          costOf("+", SFunc(Vector(SBigInt, SBigInt), SBigInt)) },
      size = {_ => SBigInt.MaxSizeInBytes },
      tree = mkPlus(BigIntConstant(big), BigIntConstant(n1)),
      Result(res, 12, 32))
  }
  test("addBigIntegerConstsCase") {
    addBigIntegerConstsCase.doReduce()
  }

  def arrayConstCase = {
    val arr1 = env("arr1").asInstanceOf[Array[Byte]]
    val col1Sym = liftConst(Colls.fromArray(arr1))
    val res = Colls.fromArray(arr1).toArray
    Case(env, "arrayConst", "arr1", ergoCtx,
      calc = {_ => col1Sym },
      cost = {_ => constCost[Coll[Byte]] },
      size = {_ => sizeOf(col1Sym) },
      tree = ByteArrayConstant(arr1), Result(res, 1, 2))
  }
  test("arrayConstCase") {
    arrayConstCase.doReduce()
  }

  def sigmaPropConstCase = {
    val resSym = dsl.proveDlog(liftConst(g1))
    val res = DLogProtocol.ProveDlog(ecp1) // NOTE! this value cannot be produced by test script
    Case(env, "sigmaPropConst", "p1", ergoCtx,
      calc = {_ => resSym },
      cost = null,
      size = {_ => CryptoConstants.groupSize.toLong },
      tree = SigmaPropConstant(p1), Result(res, 10053, 32))
  }
  test("sigmaPropConstCase") {
    sigmaPropConstCase.doReduce()
  }

  def andSigmaPropConstsCase = {
    import SigmaDslBuilder._
    val p1Sym: Rep[SigmaProp] = dsl.proveDlog(liftConst(g1))
    val p2Sym: Rep[SigmaProp] = dsl.proveDlog(liftConst(g2))
    Case(env, "andSigmaPropConsts", "p1 && p2", ergoCtx,
      calc = {_ => dsl.allZK(colBuilder.fromItems(p1Sym, p2Sym)) },
      cost = null,
      size = null,
      tree = SigmaAnd(Seq(SigmaPropConstant(p1), SigmaPropConstant(p2))),
      Result(CAND(Seq(p1, p2)), 20126, 66))
  }

  test("andSigmaPropConstsCase") {
    andSigmaPropConstsCase.doReduce()
  }

  def bigIntArray_Map_Case = {
    import SCollection._
    val res = Colls.fromArray(bigIntegerArr1).map(n => n.add(n1)).toArray
    Case(env, "bigIntArray_Map",
      "bigIntArr1.map { (i: BigInt) => i + n1 }", ergoCtx,
      calc = { ctx =>
        val vals = liftConst(Colls.fromArray(bigIntegerArr1.map(dslValue.BigInt(_))))
        vals.map(fun(n => n.add(liftConst(dslValue.BigInt(n1)))))
      },
      cost = null,
//      {_ =>
//        val arr = liftConst(bigIntArr1)
//        val opType = SFunc(Vector(SBigInt,SBigInt), SBigInt)
//        val f = fun { in: Rep[(Int, Long)] =>
//          val Pair(c, s) = in
//          val c1 = c + constCost[WBigInteger] + costOf("+", opType)
//          val c2 = costOf("+_per_item", opType) * ((s max sizeOf(liftConst(n1))) + 1L).toInt
//          c1 + c2
//        }
//        val arrSizes = colBuilder.fromArray(liftConst(Array(1L, 1L)))
//        val costs = colBuilder.replicate(arr.length, 0).zip(arrSizes).map(f)
//        constCost[Coll[WBigInteger]] + costs.sum(intPlusMonoid)
//      },
      size = {_ =>
        typeSize[BigInt] * liftConst(bigIntegerArr1).length.toLong
      },
      tree = mkMapCollection(BigIntArrayConstant(bigIntegerArr1), mkFuncValue(Vector((1,SBigInt)), ArithOp(ValUse(1,SBigInt), BigIntConstant(10L), -102))),
      Result(res, 23, 64))
  }
  test("bigIntArray_Map_Case") {
    bigIntArray_Map_Case.doReduce()
  }

  def bigIntArray_Slice_Case = {
    import SCollection._
    Case(env, "bigIntArray_Slice_Case",
      "bigIntArr1.slice(0,1)", ergoCtx,
      calc = null,
      cost = null,
      size = null,
      tree = null,
      Result(bigIntegerArr1.slice(0, 1), 21, 32))
  }
  test("bigIntArray_Slice_Case") {
    bigIntArray_Slice_Case.doReduce()
  }

//  def bigIntArray_Where_Case = {
//    import SCollection._
//    Case(env, "bigIntArray_Where_Case",
//      "bigIntArr1.where(fun (i: BigInt) = i > 0)", ergoCtx,
//      calc = null,
//      cost = null,
//      size = null,
//      tree = null,
//      Result.Ignore)
//  }
//  test("bigIntArray_Where_Case") {
//    bigIntArray_Where_Case.doReduce()
//  }

  def register_BigIntArr_Case = {
    import SCollection._
    Case(env, "register_BigIntArr_Case",
      "SELF.R4[Coll[BigInt]].get", ergoCtx,
      calc = null,
      cost = null,
      size = null,
      tree = null,
      Result(bigIntegerArr1, 2, 64L))
  }
  test("register_BigIntArr_Case") {
    measure(5) { i =>
      register_BigIntArr_Case.doReduce()
    }
    /*
    Iter 0: 3074 ms
    Iter 1: 29 ms
    Iter 2: 31 ms
    Iter 3: 26 ms
    Iter 4: 24 ms
    Total time: 3184 ms
    */
  }

  def register_BigIntArr_Map_Case = {
    import SCollection._
    Case(env, "register_BigIntArr_Map_Case",
      "SELF.R4[Coll[BigInt]].get.map { (i: BigInt) => i + n1 }", ergoCtx,
      calc = null,
      cost = null,
      size = null,
      tree = null,
      Result(bigIntegerArr1.map(i => i.add(n1)), 24, 64L))
  }
  test("register_BigIntArr_Map_Case") {
    register_BigIntArr_Map_Case.doReduce()
  }

  def register_BigIntArr_Slice_Case = {
    import SCollection._
    Case(env, "register_BinIntArr_Slice_Case",
      "SELF.R4[Coll[BigInt]].get.slice(0,1)", ergoCtx,
      calc = null,
      cost = null,
      size = null,
      tree = null,
      Result(bigIntegerArr1.slice(0,1)/*,207, 1L*/))
  }
  test("register_BigIntArr_Slice_Case") {
    register_BigIntArr_Slice_Case.doReduce()
  }

  def crowdFunding_Case = {
    import SCollection._
    import SigmaDslBuilder._
    import Box._
    import Values._
    val prover = new ErgoLikeTestProvingInterpreter()
    val backerPK  = prover.dlogSecrets(0).publicImage
    val projectPK = prover.dlogSecrets(1).publicImage

    val env = envCF ++ Seq("projectPubKey" -> projectPK, "backerPubKey" -> backerPK)
    Case(env, "crowdFunding_Case", crowdFundingScript, ergoCtx,
      { ctx: Rep[Context] =>
        val backerPubKey = liftConst(dslValue.SigmaProp(backerPK))
        val projectPubKey = liftConst(dslValue.SigmaProp(projectPK))
        val c1 = dsl.sigmaProp(ctx.HEIGHT >= toRep(timeout)).asRep[SigmaProp] && backerPubKey
        val c2 = dsl.sigmaProp(dsl.allOf(colBuilder.fromItems(
          ctx.HEIGHT < toRep(timeout),
          ctx.OUTPUTS.exists(fun { out =>
            out.value >= toRep(minToRaise) lazy_&& Thunk(out.propositionBytes === projectPubKey.propBytes)
          }))
        )).asRep[SigmaProp] && projectPubKey
        (c1 || c2)
      },
      cost = null,
      size = null,
      tree = BlockValue(Vector(
        ValDef(1,List(),SigmaPropConstant(projectPK))),
        SigmaOr(Seq(
          SigmaAnd(Seq(BoolToSigmaProp(GE(Height,IntConstant(100))),SigmaPropConstant(backerPK))),
          SigmaAnd(Seq(
            BoolToSigmaProp(AND(Vector(
              LT(Height,IntConstant(100)),
              Exists(Outputs,
                FuncValue(Vector((2,SBox)),
                  BinAnd(
                    GE(ExtractAmount(ValUse(2,SBox)),LongConstant(1000)),
                    EQ(ExtractScriptBytes(ValUse(2,SBox)), SigmaPropBytes(ValUse(1,SSigmaProp))))
                )
              )))),
            ValUse(1,SSigmaProp)
          ))))),
      Result({ TrivialProp.FalseProp }, 40686, 1L)
    )
  }
  test("crowdFunding_Case") {
    crowdFunding_Case.doReduce()
  }

  //  def register_BinIntArr_Where_Case = {
  //    import SCollection._
  //    Case(env, "contextVar_BinIntArr_Map_Case",
  //      "SELF.R4[Array[BigInt]].value.where(fun (i: BigInt) = i > 0)", ergoCtx,
  //      calc = null,
  //      cost = null,
  //      size = null,
  //      tree = null,
  //      Result.Ignore)
  //  }

}
