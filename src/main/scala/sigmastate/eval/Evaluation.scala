package sigmastate.eval

import java.math.BigInteger

import org.bouncycastle.math.ec.ECPoint
import org.ergoplatform._
import sigmastate._
import sigmastate.Values.{Value, GroupElementConstant, SigmaBoolean, Constant}
import sigmastate.lang.Terms.OperationId
import sigmastate.utxo.CostTableStat

import scala.reflect.ClassTag
import scala.util.Try
import sigmastate.SType._
import sigmastate.interpreter.CryptoConstants.EcPointType
import special.sigma.InvalidType
import scalan.{Nullable, RType}
import scalan.RType._
import sigma.types.PrimViewType
import sigmastate.basics.DLogProtocol.ProveDlog
import sigmastate.basics.{ProveDHTuple, DLogProtocol}
import special.sigma.Extensions._
import scorex.util.Extensions._
import special.SpecialPredef
import special.collection.Coll

trait Evaluation extends RuntimeCosting { IR =>
  import Context._
  import SigmaProp._
  import Coll._
  import CReplColl._
  import Box._
  import AvlTree._
  import CollBuilder._
  import SigmaDslBuilder._
  import CostedBuilder._
  import MonoidBuilder._
  import WBigInteger._
  import WArray._
  import WOption._
  import GroupElement._
  import Liftables._
  import WSpecialPredef._

  val okPrintEvaluatedEntries: Boolean = false

  private val ContextM = ContextMethods
  private val SigmaM = SigmaPropMethods
  private val CollM = CollMethods
  private val BoxM = BoxMethods
  private val AvlM = AvlTreeMethods
  private val CBM = CollBuilderMethods
  private val SDBM = SigmaDslBuilderMethods
  private val AM = WArrayMethods
  private val OM = WOptionMethods
  private val BIM = WBigIntegerMethods
  private val SPCM = WSpecialPredefCompanionMethods

  def isValidCostPrimitive(d: Def[_]): Unit = d match {
    case _: Const[_] =>
    case _: SizeData[_,_] =>
    case _: Tup[_,_] | _: First[_,_] | _: Second[_,_] =>
    case _: FieldApply[_] =>
    case _: IntPlusMonoid =>
    case _: Lambda[_,_] =>
    case _: ThunkDef[_] =>
    case ApplyUnOp(_: NumericToLong[_] | _: NumericToInt[_], _) =>
    case ApplyBinOp(_: NumericPlus[_] | _: NumericTimes[_] | _: OrderingMax[_] | _: IntegralDivide[_] ,_,_) =>
    case ContextM.SELF(_) | ContextM.OUTPUTS(_) | ContextM.INPUTS(_) | ContextM.dataInputs(_) | ContextM.LastBlockUtxoRootHash(_) |
         ContextM.getVar(_,_,_) /*| ContextM.cost(_) | ContextM.dataSize(_)*/ =>
    case SigmaM.propBytes(_) =>
    case CollM.length(_) | CollM.map(_,_) | CollM.sum(_,_) | CollM.zip(_,_) | CollM.slice(_,_,_) | CollM.apply(_,_) | CollM.append(_,_) =>
    case CBM.replicate(_,_,_) | CBM.fromItems(_,_,_) =>
    case BoxM.propositionBytes(_) | BoxM.bytesWithoutRef(_) /*| BoxM.cost(_) | BoxM.dataSize(_)*/ | BoxM.getReg(_,_,_) =>
//    case AvlM.dataSize(_) =>
    case OM.get(_) | OM.getOrElse(_,_) | OM.fold(_,_,_) | OM.isDefined(_) =>
    case _: CostOf | _: SizeOf[_] =>
    case _: Upcast[_,_] =>
    case _: Apply[_,_] =>
    case SPCM.some(_) =>
    case _ => !!!(s"Invalid primitive in Cost function: $d")
  }

  def verifyCalcFunc[A](f: Rep[Context => A], eA: Elem[A]) = {
    if (f.elem.eRange != eA)
      !!!(s"Expected function of type ${f.elem.eDom.name} => ${eA.name}, but was $f: ${f.elem.name}")
  }

  def verifyCostFunc(costF: Rep[((Int, Size[Context])) => Int]): Try[Unit] = {
    val Def(Lambda(lam,_,_,_)) = costF
    Try { lam.scheduleAll.foreach(te => isValidCostPrimitive(te.rhs)) }
  }

  def findIsProven[T](f: Rep[Context => T]): Option[Sym] = {
    val Def(Lambda(lam,_,_,_)) = f
    val ok = lam.scheduleAll.find(te => te.rhs match {
      case SigmaM.isValid(_) => true
      case _ => false
    }).map(_.sym)
    ok
  }

  def verifyIsProven[T](f: Rep[Context => T]): Try[Unit] = {
    val isProvenOpt = findIsProven(f)
    Try {
      isProvenOpt match {
        case Some(s) =>
          if (f.getLambda.y != s) !!!(s"Sigma.isProven found in none-root position", s)
        case None =>
      }
    }
  }
  object IsTupleFN {
    def unapply(fn: String): Nullable[Byte] = {
      if (fn.startsWith("_")) Nullable[Byte](fn.substring(1).toByte)
      else Nullable.None.asInstanceOf[Nullable[Byte]]
    }
  }
  import sigmastate._
  import special.sigma.{Context => SigmaContext}

  type ContextFunc[T <: SType] = SigmaContext => Value[T]

  val sigmaDslBuilderValue: CostingSigmaDslBuilder
  val costedBuilderValue: special.collection.CostedBuilder
  val monoidBuilderValue: special.collection.MonoidBuilder

  def getDataEnv: DataEnv = {
    val env = Map[Sym, AnyRef](
      RWSpecialPredef -> SpecialPredef,
      sigmaDslBuilder -> sigmaDslBuilderValue,
      sigmaDslBuilder.Colls -> sigmaDslBuilderValue.Colls,
      costedBuilder -> costedBuilderValue,
      costedBuilder.monoidBuilder -> monoidBuilderValue,
      costedBuilder.monoidBuilder.intPlusMonoid -> monoidBuilderValue.intPlusMonoid,
      costedBuilder.monoidBuilder.longPlusMonoid -> monoidBuilderValue.longPlusMonoid
    )
    env
  }

  case class EvaluatedEntry(env: DataEnv, sym: Sym, value: AnyRef)

  def printEnvEntry(sym: Sym, value: AnyRef) = {
    def trim[A](arr: Array[A]) = arr.take(arr.length min 100)
    def show(x: Any) = x match {
      case arr: Array[_] => s"Array(${trim(arr).mkString(",")})"
      case col: special.collection.Coll[_] => s"Coll(${trim(col.toArray).mkString(",")})"
      case p: SGroupElement => p.showToString
      case ProveDlog(GroupElementConstant(g)) => s"ProveDlog(${showECPoint(g)})"
      case ProveDHTuple(
              GroupElementConstant(g), GroupElementConstant(h), GroupElementConstant(u), GroupElementConstant(v)) =>
        s"ProveDHT(${showECPoint(g)},${showECPoint(h)},${showECPoint(u)},${showECPoint(v)})"
      case _ => x.toString
    }
    sym match {
      case x if x.isVar => s"Var($sym -> ${show(value)})"
      case Def(Lambda(_, _, x, y)) => s"Lam($x => $y)"
      case _ => s"$sym -> ${show(value)}"
    }
  }

  def onEvaluatedGraphNode(env: DataEnv, sym: Sym, value: AnyRef): Unit = {
    if (okPrintEvaluatedEntries)
      println(printEnvEntry(sym, value))
  }

  def compile[T <: SType](dataEnv: Map[Sym, AnyRef], f: Rep[Context => T#WrappedType]): ContextFunc[T] = {

    def evalSizeData(data: SizeData[_,_], dataEnv: DataEnv): Any = {
      val info = dataEnv(data.sizeInfo)
      data.eVal match {
        case _: BaseElem[_] => info.asInstanceOf[Long]
        case _: PairElem[_,_] =>
          val (l, r) = info.asInstanceOf[(Long,Long)]
          l + r
        case _: CollElem[_,_] =>
          val coll = info.asInstanceOf[SColl[Long]]
          coll.sum(longPlusMonoidValue)
        case _: WOptionElem[_,_] =>
          val sizeOpt = info.asInstanceOf[Option[Long]]
          sizeOpt.getOrElse(0L)
        case _: EntityElem[_] =>
          info.asInstanceOf[Long]
        case _ => error(s"Cannot evalSizeData($data)")
      }
    }

    def evaluate(ctxSym: Rep[Context], te: TableEntry[_]): EnvRep[_] = EnvRep { dataEnv =>
      object In { def unapply(s: Sym): Option[Any] = Some(dataEnv(s)) }
      def out(v: Any): (DataEnv, Sym) = { val vBoxed = v.asInstanceOf[AnyRef]; (dataEnv + (te.sym -> vBoxed), te.sym) }
      try {
        var startTime = if (okMeasureOperationTime) System.nanoTime() else 0L
        val res: (DataEnv, Sym) = te.rhs match {
          case d @ ContextM.getVar(ctx @ In(ctxObj: CostingDataContext), _, elem) =>
            val mc = d.asInstanceOf[MethodCall]
            val declaredTpe = elemToSType(elem)
            val valueInCtx = invokeUnlifted(ctx.elem, mc, dataEnv)
            val data = valueInCtx match {
              case Some(Constant(v, `declaredTpe`)) =>
                Some(Evaluation.toDslData(v, declaredTpe, ctxObj.isCost)(IR))
              case opt @ Some(v) => opt
              case None => None
              case _ => throw new InvalidType(s"Expected Constant($declaredTpe) but found $valueInCtx")
            }
            out(data)
          case d @ BoxM.getReg(box, _, elem) =>
            val ctxObj = dataEnv(ctxSym).asInstanceOf[CostingDataContext]
            val mc = d.asInstanceOf[MethodCall]
            val declaredTpe = elemToSType(elem)
            val valueInReg = invokeUnlifted(box.elem, mc, dataEnv)
            val data = valueInReg match {
              case Some(Constant(v, `declaredTpe`)) =>
                Some(Evaluation.toDslData(v, declaredTpe, ctxObj.isCost)(IR))
              case Some(v) =>
                valueInReg
              case None => None
              case _ => throw new InvalidType(
                s"Expected Some(Constant($declaredTpe)) but found $valueInReg value of register: $d")
            }
            out(data)
          case Const(x) => out(x.asInstanceOf[AnyRef])
          case sd: SizeData[_,_] => out(evalSizeData(sd, dataEnv))
          case Tup(In(a), In(b)) => out((a,b))
          case First(In(p: Tuple2[_,_])) => out(p._1)
          case Second(In(p: Tuple2[_,_])) => out(p._2)
          case FieldApply(In(data), IsTupleFN(i)) => data match {
            case coll: special.collection.Coll[a] =>
              out(coll(i - 1))
            case tup: Product =>
              out(tup.productElement(i - 1))
          }

          case wc: LiftedConst[_,_] => out(wc.constValue)

          case _: SigmaDslBuilder | _: CollBuilder | _: CostedBuilder | _: IntPlusMonoid | _: LongPlusMonoid |
               _: WSpecialPredefCompanion =>
            out(dataEnv.getOrElse(te.sym, !!!(s"Cannot resolve companion instance for $te")))

          case SigmaM.isValid(In(prop: AnyRef)) =>
            out(prop)

          case SDBM.substConstants(_,
            In(input: special.collection.Coll[Byte]@unchecked),
            In(positions: special.collection.Coll[Int]@unchecked),
            In(newVals: special.collection.Coll[Any]@unchecked), _) =>
            val typedNewVals = newVals.toArray.map(v => builder.liftAny(v) match {
              case Nullable(v) => v
              case _ => sys.error(s"Cannot evaluate substConstants($input, $positions, $newVals): cannot lift value $v")
            })
            val byteArray = SubstConstants.eval(input.toArray, positions.toArray, typedNewVals)
            out(sigmaDslBuilderValue.Colls.fromArray(byteArray))

          case AM.length(In(arr: Array[_])) => out(arr.length)
          case CBM.replicate(In(b: special.collection.CollBuilder), In(n: Int), xSym @ In(x)) =>
            out(b.replicate(n, x)(asType[Any](xSym.elem.sourceType)))

          case SPCM.some(In(v)) => out(Some(v))
          case SPCM.none(_) => out(None)

          // NOTE: This is a fallback rule which should be places AFTER all other MethodCall patterns
          case mc @ MethodCall(obj, m, args, _) =>
            val dataRes = obj.elem match {
              case _: CollElem[_, _] => mc match {
                case CollMethods.flatMap(xs, f) =>
                  val newMC = mc.copy(args = mc.args :+ f.elem.eRange)(mc.selfType, mc.isAdapterCall)
                  invokeUnlifted(obj.elem, newMC, dataEnv)
                case _ =>
                  invokeUnlifted(obj.elem, mc, dataEnv)
              }
              case _ =>
                invokeUnlifted(obj.elem, mc, dataEnv)
            }
            val res = dataRes match {
              case Constant(v, _) => v
              case v => v
            }
            out(res)
          case ApplyUnOp(op: UnOp[l,r], In(x)) =>
            out(op.applySeq(x).asInstanceOf[AnyRef])
          case ApplyBinOp(op: BinOp[l,r], In(x), In(y)) =>
            out(op.applySeq(x, y).asInstanceOf[AnyRef])
          case ApplyBinOpLazy(op, In(x: Boolean), In(y)) if op == Or =>
            if (x) out(true)
            else {
              val th = y.asInstanceOf[() => Any]
              out(th())
            }
          case ApplyBinOpLazy(op, In(x: Boolean), In(y)) if op == And =>
            if (x) {
              val th = y.asInstanceOf[() => Any]
              out(th())
            } else
              out(false)
          case IfThenElseLazy(In(cond: Boolean), In(t), In(e)) =>
            if (cond) {
              val th = t.asInstanceOf[() => Any]
              out(th())
            } else {
              val th = e.asInstanceOf[() => Any]
              out(th())
            }

          case Lambda(l, _, x, y) =>
            val f = (ctx: AnyRef) => {
              val resEnv = l.schedule.foldLeft(dataEnv + (x -> ctx)) { (env, te) =>
                val (e, _) = evaluate(ctxSym, te).run(env)
                e
              }
              val res = resEnv(y)
              res
            }
            out(f)
          case Apply(In(_f), In(x: AnyRef), _) =>
            val f = _f.asInstanceOf[AnyRef => Any]
            out(f(x))
          case First(In(p: Tuple2[_,_])) => out(p._1)
          case Second(In(p: Tuple2[_,_])) => out(p._2)
          case ThunkDef(y, schedule) =>
            val th = () => {
              val resEnv = schedule.foldLeft(dataEnv) { (env, te) =>
                val (e, _) = evaluate(ctxSym, te).run(env)
                e
              }
              resEnv(y)
            }
            out(th)

          case SDBM.sigmaProp(_, In(isValid: Boolean)) =>
            val res = CSigmaProp(sigmastate.TrivialProp(isValid))
            out(res)
          case SDBM.proveDlog(_, In(g: EcPointType)) =>
            val res = CSigmaProp(DLogProtocol.ProveDlog(g))
            out(res)
          case SDBM.proveDHTuple(_, In(g: EcPointType), In(h: EcPointType), In(u: EcPointType), In(v: EcPointType)) =>
            val res = CSigmaProp(ProveDHTuple(g, h, u, v))
            out(res)
          case SDBM.avlTree(_, In(flags: Byte),
                           In(digest: SColl[Byte]@unchecked), In(keyLength: Int),
                           In(valueLengthOpt: Option[Int]@unchecked)) =>
            val res = sigmaDslBuilderValue.avlTree(flags, digest, keyLength, valueLengthOpt)
            out(res)

          case CReplCollCtor(valueSym @ In(value), In(len: Int)) =>
            val res = sigmaDslBuilderValue.Colls.replicate(len, value)(asType[Any](valueSym.elem.sourceType))
            out(res)
          case costOp: CostOf =>
            out(costOp.eval)
          case SizeOf(sym @ In(data)) =>
            val tpe = elemToSType(sym.elem)
            val size = tpe match {
//              case SAvlTree =>
//                data.asInstanceOf[special.sigma.AvlTree].dataSize
              case _ => data match {
                case w: WrapperOf[_] =>
                  tpe.dataSize(w.wrappedValue.asWrappedType)
                case _ =>
                  tpe.dataSize(data.asWrappedType)
              }
            }
            out(size)
          case TypeSize(tpe) =>
            assert(tpe.isConstantSize)
            val size = tpe.dataSize(SType.DummyValue)
            out(size)
          case Downcast(In(from), eTo) =>
            val tpe = elemToSType(eTo).asNumType
            if (tpe == SBigInt)
              out(sigmaDslBuilderValue.BigInt(SBigInt.downcast(from.asInstanceOf[AnyVal])))
            else
              out(tpe.downcast(from.asInstanceOf[AnyVal]))
          case Upcast(In(from), eTo) =>
            val tpe = elemToSType(eTo).asNumType
            if (tpe == SBigInt)
              out(sigmaDslBuilderValue.BigInt(SBigInt.upcast(from.asInstanceOf[AnyVal])))
            else
              out(tpe.upcast(from.asInstanceOf[AnyVal]))

          case SimpleStruct(_, fields) =>
            val items = fields.map { case (_, In(fieldValue)) => fieldValue }.toArray
            out(sigmaDslBuilderValue.Colls.fromArray(items)(AnyType))

          case _ =>
            !!!(s"Don't know how to evaluate($te)")
        }
        if (okMeasureOperationTime) {
          val endTime = System.nanoTime()
          val estimatedTime = endTime - startTime
          te.sym.getMetadata(OperationIdKey) match {
            case Some(opId: OperationId) =>
              if (opId.opType.tRange.isCollection) {
                val col = res._1(res._2).asInstanceOf[SColl[Any]]
                val colTime = if (col.length > 1) estimatedTime / col.length else estimatedTime
                CostTableStat.addOpTime(opId, colTime, col.length)
              }
              else
                CostTableStat.addOpTime(opId, estimatedTime, len = 1)
            case _ =>
          }
        }
        onEvaluatedGraphNode(res._1, res._2, res._1(res._2))
        res
      }
      catch {
        case e: Throwable =>
          !!!(s"Error in Evaluation.compile.evaluate($te)", e)
      }
    }

    val res = (ctx: SContext) => {
      val g = new PGraph(f)
      val ctxSym = f.getLambda.x
      val resEnv = g.schedule.foldLeft(dataEnv + (ctxSym -> ctx)) { (env, te) =>
        val (e, _) = evaluate(ctxSym, te).run(env)
        e
      }
      val fun = resEnv(f).asInstanceOf[SigmaContext => Any]
      fun(ctx) match {
        case sb: SigmaBoolean => builder.liftAny(sb).get
        case v: Value[_] => v
        case x =>
          val eRes = f.elem.eRange
          val tpeRes = elemToSType(eRes)
          val tRes = Evaluation.stypeToRType(tpeRes)
          val treeType = Evaluation.toErgoTreeType(tRes)
          val constValue = Evaluation.fromDslData(x, treeType)
          builder.mkConstant[SType](constValue.asInstanceOf[SType#WrappedType], tpeRes)
      }
    }
    res.asInstanceOf[ContextFunc[T]]
  }
}

object Evaluation {
  import special.sigma._
  import special.collection._
  import ErgoLikeContext._
  
  case class GenericRType[T <: AnyRef](classTag : ClassTag[T]) extends RType[T]

  def AnyRefRType[T <: AnyRef: ClassTag]: RType[T] = GenericRType[T](scala.reflect.classTag[T])

  def stypeToRType[T <: SType](t: T): RType[T#WrappedType] = (t match {
    case SBoolean => BooleanType
    case SByte => ByteType
    case SShort => ShortType
    case SInt => IntType
    case SLong => LongType
    case SString => StringType
    case SAny => AnyType
    case SBigInt => BigIntRType
    case SBox => BoxRType
    case SContext => ContextRType
    case SHeader => HeaderRType
    case SPreHeader => PreHeaderRType
    case SGroupElement => GroupElementRType
    case SAvlTree => AvlTreeRType
    case SSigmaProp => SigmaPropRType
    case STuple(Seq(tpeA, tpeB)) =>
      pairRType(stypeToRType(tpeA), stypeToRType(tpeB))
    case STuple(items) =>
      val types = items.toArray
      tupleRType(types.map(t => stypeToRType(t).asInstanceOf[SomeType]))
    case c: SCollectionType[a] => collRType(stypeToRType(c.elemType))
    case o: SOption[a] => optionRType(stypeToRType(o.elemType))
    case SFunc(Seq(tpeArg), tpeRange, Nil) => funcRType(stypeToRType(tpeArg), stypeToRType(tpeRange))
    case _ => sys.error(s"Don't know how to convert SType $t to RType")
  }).asInstanceOf[RType[T#WrappedType]]

  def rtypeToSType[T](t: RType[T]): SType = t match {
    case BooleanType => SBoolean
    case ByteType => SByte
    case ShortType => SShort
    case IntType => SInt
    case LongType => SLong
    case StringType => SString
    case AnyType => SAny

    case BigIntegerRType => SBigInt
    case BigIntRType => SBigInt

    case ECPointRType => SGroupElement
    case GroupElementRType => SGroupElement

    case AvlTreeRType => SAvlTree
    case ot: OptionType[_] => sigmastate.SOption(rtypeToSType(ot.tA))
    case BoxRType => SBox
    case ContextRType => SContext
    case HeaderRType => SHeader
    case PreHeaderRType => SPreHeader
    case SigmaPropRType => SSigmaProp
    case SigmaBooleanRType => SSigmaProp
    case tup: TupleType => STuple(tup.items.map(t => rtypeToSType(t)).toIndexedSeq)
    case at: ArrayType[_] => SCollection(rtypeToSType(at.tA))
    case ct: CollType[_] => SCollection(rtypeToSType(ct.tItem))
    case ft: FuncType[_,_] => SFunc(rtypeToSType(ft.tDom), rtypeToSType(ft.tRange))
    case pt: PairType[_,_] => STuple(rtypeToSType(pt.tFst), rtypeToSType(pt.tSnd))
    case pvt: PrimViewType[_,_] => rtypeToSType(pvt.tVal)
    case _ => sys.error(s"Don't know how to convert RType $t to SType")
  }

  /** Tries to reconstruct RType of the given value.
    * If not successfull returns failure. */
  def rtypeOf(value: Any): Try[RType[_]] = Try { value match {
    case arr if arr.getClass.isArray =>
      val itemClass = arr.getClass.getComponentType
      if (itemClass.isPrimitive) {
        val itemTag = ClassTag[Any](itemClass)
        RType.fromClassTag(itemTag)
      } else
        sys.error(s"Cannot compute rtypeOf($value): non-primitive type of array items")

    case coll: Coll[_] => collRType(coll.tItem)
    
    // all primitive types
    case v: Boolean => BooleanType
    case v: Byte  => ByteType
    case v: Short => ShortType
    case v: Int   => IntType
    case v: Long  => LongType
    case v: Char  => CharType
    case v: Float  => FloatType
    case v: Double  => DoubleType
    case v: String  => StringType
    case v: Unit  => UnitType

    case v: BigInteger => BigIntegerRType
    case n: special.sigma.BigInt => BigIntRType

    case v: ECPoint => ECPointRType
    case ge: GroupElement => GroupElementRType

    case b: ErgoBox => ErgoBoxRType
    case b: Box => BoxRType

    case avl: AvlTreeData => AvlTreeDataRType
    case avl: AvlTree => AvlTreeRType

    case sb: SigmaBoolean => SigmaBooleanRType
    case p: SigmaProp => SigmaPropRType

    case _ =>
      sys.error(s"Don't know how to compute typeOf($value)")
  }}

  /** Generic translation of any ErgoDsl type to the corresponding type used in ErgoTree. */
  def toErgoTreeType(dslType: RType[_]): RType[_] = dslType match {
    case p: PrimitiveType[_] => p
    case w: WrapperType[_] =>
      w match {
        case BigIntRType => BigIntegerRType
        case GroupElementRType => ECPointRType
        case SigmaPropRType => SigmaBooleanRType
        case BoxRType => ErgoBoxRType
        case AvlTreeRType => AvlTreeDataRType
        case ContextRType => ErgoLikeContextRType
        case _ => sys.error(s"Unknown WrapperType: $w")
      }
    case p: ArrayType[_] => arrayRType(toErgoTreeType(p.tA))
    case p: OptionType[_] => optionRType(toErgoTreeType(p.tA))
    case p: CollType[_] => arrayRType(toErgoTreeType(p.tItem))
    case p: PairType[_,_] => tupleRType(Array(toErgoTreeType(p.tFst), toErgoTreeType(p.tSnd)))
    case p: EitherType[_,_] => eitherRType(toErgoTreeType(p.tA), toErgoTreeType(p.tB))
    case p: FuncType[_,_] => funcRType(toErgoTreeType(p.tDom), toErgoTreeType(p.tRange))
    case t: TupleType => tupleRType(t.items.map(x => toErgoTreeType(x)))
    case HeaderRType | PreHeaderRType => dslType
    case AnyType | AnyRefType | NothingType | StringType => dslType
    case _ =>
      sys.error(s"Don't know how to toErgoTreeType($dslType)")
  }

  /** Generic converter from types used in SigmaDsl to types used in ErgoTree values.
    * @param tRes should describe ErgoTree type (i.e. it can be obtained using toErgoTreeType method)*/
  def fromDslData[T](value: Any, tRes: RType[T]): T = {
    val res = (value, tRes) match {
      case (w: WrapperOf[_], _) => w.wrappedValue
      case (coll: Coll[a], tarr: ArrayType[a1]) =>
        val tItem = tarr.tA
        coll.map[a1](x => fromDslData(x, tItem))(tItem).toArray
      case (tup: Tuple2[a,b], tTup: TupleType) =>
        val x = fromDslData(tup._1, tTup.items(0))
        val y = fromDslData(tup._2, tTup.items(1))
        Array[Any](x, y)
      case _ => value
    }
    res.asInstanceOf[T]
  }

  /** Convert SigmaDsl representation of tuple to ErgoTree representation. */
  def fromDslTuple(value: Any, tupleTpe: STuple): Array[Any] = value match {
    case t: Tuple2[_,_] => Array[Any](t._1, t._2)
    case a: Array[Any] => a
    case _ =>
      sys.error(s"Cannot execute fromDslTuple($value, $tupleTpe)")
  }

  /** Generic converter from types used in ErgoTree values to types used in ErgoDsl. */
  def toDslData(value: Any, tpe: SType, isCost: Boolean)(implicit IR: Evaluation): Any = {
    val dsl = IR.sigmaDslBuilderValue
    (value, tpe) match {
      case (c: Constant[_], tpe) => toDslData(c.value, c.tpe, isCost)
      case (_, STuple(Seq(tpeA, tpeB))) =>
        value match {
          case tup: Tuple2[_,_] =>
            val valA = toDslData(tup._1, tpeA, isCost)
            val valB = toDslData(tup._2, tpeB, isCost)
            (valA, valB)
          case arr: Array[Any] =>
            val valA = toDslData(arr(0), tpeA, isCost)
            val valB = toDslData(arr(1), tpeB, isCost)
            (valA, valB)
        }
      case (arr: Array[a], STuple(items)) =>
        val res = arr.zip(items).map { case (x, t) => toDslData(x, t, isCost)}
        dsl.Colls.fromArray(res)(RType.AnyType)
      case (arr: Array[a], SCollectionType(elemType)) =>
        implicit val elemRType: RType[SType#WrappedType] = Evaluation.stypeToRType(elemType)
        elemRType.asInstanceOf[RType[_]] match {
          case _: CollType[_] | _: TupleType | _: PairType[_,_] | _: WrapperType[_] =>
            val testArr = arr.map(x => toDslData(x, elemType, isCost).asWrappedType).toArray(elemRType.classTag)
            dsl.Colls.fromArray(testArr.asInstanceOf[Array[SType#WrappedType]])
          case _ =>
            dsl.Colls.fromArray(arr.asInstanceOf[Array[SType#WrappedType]])
        }
      case (b: ErgoBox, SBox) => b.toTestBox(isCost)
      case (n: BigInteger, SBigInt) =>
        dsl.BigInt(n)
      case (p: ECPoint, SGroupElement) => dsl.GroupElement(p)
      case (t: SigmaBoolean, SSigmaProp) => dsl.SigmaProp(t)
      case (t: AvlTreeData, SAvlTree) => CAvlTree(t)
      case (x, _) => x
    }
  }

}
