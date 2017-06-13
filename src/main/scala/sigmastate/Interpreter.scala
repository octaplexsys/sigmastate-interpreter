package sigmastate

import edu.biu.scapi.primitives.dlog.DlogGroup
import edu.biu.scapi.primitives.dlog.bc.BcDlogECFp
import org.bitbucket.inkytonik.kiama.attribution.Attribution
import org.bitbucket.inkytonik.kiama.relation.Tree
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.{everywherebu, everywheretd, rule}
import org.bitbucket.inkytonik.kiama.rewriting.Strategy
import scapi.sigma.rework.DLogProtocol.DLogNode
import scapi.sigma.rework.DLogProtocol
import scorex.crypto.hash.Blake2b256
import sigmastate.utils.Helpers

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.Try

trait Context[C <: Context[C]] {
  val extension: ContextExtension

  def withExtension(newExtension: ContextExtension): C
}


/**
  * Variables to be put into context
  */
case class ContextExtension(values: Map[Int, _ <: Value])

/**
  * Proof generated by a prover along with possible context extensions
  */
case class ProverResult[ProofT <: UncheckedTree](proof: ProofT, extension: ContextExtension)

trait Interpreter {
  type CTX <: Context[CTX]
  type StateT <: StateTree
  type SigmaT <: SigmaTree

  type ProofT = UncheckedTree //todo:  ProofT <: UncheckedTree ?

  val dlogGroup: DlogGroup = new BcDlogECFp()

  def maxDepth: Int

  /**
    * implementation-specific tree reductions, to be defined in descendants
    *
    * @param tree - a tree to process-
    * @param ctx  - context instance
    * @return - processed tree
    */
  def specificPhases(tree: SigmaStateTree, ctx: CTX): SigmaStateTree

  protected def contextSubst(ctx: CTX): Strategy = everywherebu(rule[SigmaStateTree] {
    case CustomByteArray(tag: Int) if ctx.extension.values.contains(tag) => ctx.extension.values(tag)
  })

  protected val rels: Strategy = everywherebu(rule[SigmaStateTree] {
    case EQ(l: Value, r: Value) => BooleanConstantNode.fromBoolean(l == r)
    case NEQ(l: Value, r: Value) => BooleanConstantNode.fromBoolean(l != r)
    case GT(l: IntLeaf, r: IntLeaf) => BooleanConstantNode.fromBoolean(l.value > r.value)
    case GE(l: IntLeaf, r: IntLeaf) => BooleanConstantNode.fromBoolean(l.value >= r.value)
    case LT(l: IntLeaf, r: IntLeaf) => BooleanConstantNode.fromBoolean(l.value < r.value)
    case LE(l: IntLeaf, r: IntLeaf) => BooleanConstantNode.fromBoolean(l.value <= r.value)
  })

  protected val ops: Strategy = everywherebu(rule[SigmaStateTree] {
    case Plus(l: IntLeaf, r: IntLeaf) => IntLeaf(l.value + r.value)
    case Minus(l: IntLeaf, r: IntLeaf) => IntLeaf(l.value - r.value)
    case Xor(l: ByteArrayLeaf, r: ByteArrayLeaf) =>
      assert(l.value.length == r.value.length)
      ByteArrayLeaf(Helpers.xor(l.value, r.value))
    case Append(l: ByteArrayLeaf, r: ByteArrayLeaf) =>
      require(l.value.length + r.value.length < 10000) //todo: externalize this maximum intermediate value length limit
      ByteArrayLeaf(l.value ++ r.value)
    case CalcBlake2b256(l: ByteArrayLeaf) => ByteArrayLeaf(Blake2b256(l.value))
  })

  protected val conjs: Strategy = everywherebu(rule[SigmaStateTree] {

    case AND(children) =>

      @tailrec
      def iterChildren(children: Seq[SigmaStateTree],
                       currentBuffer: mutable.Buffer[SigmaStateTree]): mutable.Buffer[SigmaStateTree] = {
        if (children.isEmpty) currentBuffer else children.head match {
          case FalseConstantNode => mutable.Buffer(FalseConstantNode)
          case TrueConstantNode => iterChildren(children.tail, currentBuffer)
          case s: SigmaStateTree => iterChildren(children.tail, currentBuffer += s)
        }
      }

      val reduced = iterChildren(children, mutable.Buffer())

      reduced.size match {
        case i: Int if i == 0 => TrueConstantNode
        case i: Int if i == 1 => reduced.head
        case _ =>
          if (reduced.forall(_.isInstanceOf[SigmaTree]))
            CAND(reduced.map(_.asInstanceOf[SigmaTree]))
          else AND(reduced)
      }


    case OR(children) =>
      @tailrec
      def iterChildren(children: Seq[SigmaStateTree],
                       currentBuffer: mutable.Buffer[SigmaStateTree]): mutable.Buffer[SigmaStateTree] = {
        if (children.isEmpty) currentBuffer else children.head match {
          case TrueConstantNode => mutable.Buffer(TrueConstantNode)
          case FalseConstantNode => iterChildren(children.tail, currentBuffer)
          case s: SigmaStateTree => iterChildren(children.tail, currentBuffer += s)
        }
      }

      val reduced = iterChildren(children, mutable.Buffer())

      reduced.size match {
        case i: Int if i == 0 => FalseConstantNode
        case i: Int if i == 1 => reduced.head
        case i: Int if i == 2 =>
          if (reduced.forall(_.isInstanceOf[SigmaTree]))
            COR2(reduced.head.asInstanceOf[SigmaTree], reduced.tail.head.asInstanceOf[SigmaTree])
          else OR(reduced)
        case _ =>
          if (reduced.forall(_.isInstanceOf[SigmaTree]))
            ??? //todo: COR for > 2 args
          else OR(reduced)
      }
  })

  //todo: cost analysis
  def reduceToCrypto(exp: SigmaStateTree, context: CTX): Try[SigmaStateTree] = Try({
    val afterContextSubst = contextSubst(context)(exp).get.asInstanceOf[SigmaStateTree]
    val afterSpecific = specificPhases(afterContextSubst, context)
    val afterOps = ops(afterSpecific).get.asInstanceOf[SigmaStateTree]
    val afterRels = rels(afterOps).get.asInstanceOf[SigmaStateTree]
    conjs(afterRels).get
  }.asInstanceOf[SigmaStateTree])


  def evaluate(exp: SigmaStateTree, context: CTX, proof: UncheckedTree, challenge: ProofOfKnowledge.Message): Try[Boolean] = Try {
    val cProp = reduceToCrypto(exp, context).get
    cProp match {
      case TrueConstantNode => true
      case FalseConstantNode => false
      case _ =>
        proof match {
          case NoProof => false
          case sp: UncheckedSigmaTree[_] => sp.proposition == cProp && sp.verify()
        }
    }
  }

  def verify(exp: SigmaStateTree,
             context: CTX,
             proverResult: ProverResult[ProofT],
             challenge: ProofOfKnowledge.Message): Try[Boolean] = {
    val ctxv = context.withExtension(proverResult.extension)
    evaluate(exp, ctxv, proverResult.proof, challenge)
  }
}


trait ProverInterpreter extends Interpreter {

  val contextExtenders: Map[Int, ByteArrayLeaf]

  def enrichContext(tree: SigmaStateTree): ContextExtension = {
    val targetName = CustomByteArray.getClass.getSimpleName.replace("$", "")

    val ce = new Tree(tree).nodes.flatMap { n =>
      if (n.productPrefix == targetName) {
        val tag = n.productIterator.next().asInstanceOf[Int]
        contextExtenders.get(tag).map(v => tag -> v)
      } else None
    }.toMap

    ContextExtension(ce)
  }

  protected def prove(unprovenTree: UnprovenTree): ProofT

  def normalizeUnprovenTree(unprovenTree: UnprovenTree): UnprovenTree

  def prove(exp: SigmaStateTree, context: CTX, challenge: ProofOfKnowledge.Message): Try[ProverResult[ProofT]] = Try {
    val candidateProp = reduceToCrypto(exp, context).get

    val (cProp, ext) = (candidateProp.isInstanceOf[SigmaT] match {
      case true => (candidateProp, ContextExtension(Map()))
      case false =>
        val extension = enrichContext(candidateProp)
        //todo: no need for full reduction here probably
        (reduceToCrypto(candidateProp, context.withExtension(extension)).get, extension)
    }).ensuring{res =>
      res._1.isInstanceOf[BooleanConstantNode] ||
        res._1.isInstanceOf[CAND] ||
        res._1.isInstanceOf[COR2] ||
        res._1.isInstanceOf[DLogNode]}


    ProverResult(cProp match {
      case tree: BooleanConstantNode =>
        tree match {
          case TrueConstantNode => NoProof
          case FalseConstantNode => ???
        }
      case _ =>
        val ct = TreeConversion.convertToUnproven(cProp.asInstanceOf[SigmaT]).withChallenge(challenge)
        val toProve = normalizeUnprovenTree(ct)
        prove(toProve)
    }, ext)
  }
}

object TreeConversion extends Attribution {

  //to be applied bottom up, converts SigmaTree => UnprovenTree
  val convertToUnproven: SigmaTree => UnprovenTree = attr {
    case CAND(sigmaTrees) => CAndUnproven(CAND(sigmaTrees), None, sigmaTrees.map(convertToUnproven))
    case COR2(left, right) => COr2Unproven(COR2(left, right), None, convertToUnproven(left), convertToUnproven(right))
    case ci: DLogNode => SchnorrUnproven(None, simulated = false, ci)
  }

  val proving: Seq[DLogProtocol.DLogProverInput] => UnprovenTree => UncheckedTree = paramAttr { secrets => {
    case SchnorrUnproven(Some(challenge), simulated, proposition) =>
      if (simulated) {
        SchnorrSigner(proposition.asInstanceOf[DLogNode],None).prove(challenge)
      } else {
        val privKey = secrets.find(_.publicImage.h == proposition.h).get
        SchnorrSigner.generate(privKey).prove(challenge)
      }

    case CAndUnproven(proposition, Some(challenge), children) =>
      val proven = children.map(proving(secrets))
      CAndUncheckedNode(proposition, challenge, proven)

    case COr2Unproven(proposition, Some(challenge), leftChild, rightChild) =>
      assert(Helpers.xor(leftChild.challengeOpt.get, rightChild.challengeOpt.get).sameElements(challenge))

      COr2UncheckedNode(proposition, challenge, proving(secrets)(leftChild), proving(secrets)(rightChild))
    case _ => ???
  }
  }
}

trait DLogProverInterpreter extends ProverInterpreter {
  override type SigmaT = SigmaTree
  override type ProofT = UncheckedTree

  val secrets: Seq[DLogProtocol.DLogProverInput]

  //to be applied bottom up, marks whether simulation is needed for a sigma-protocol
  val markSimulated: Strategy = rule[UnprovenTree] {
    case su: SchnorrUnproven =>
      val secretKnown = secrets.exists(_.publicImage.h == su.proposition.h)
      su.copy(simulated = !secretKnown)
  }

  //to be applied down from the top node
  val challengeDisperse: Strategy = rule[UnprovenTree] {
    case cand: CAndUnproven if cand.challengeOpt.isDefined =>
      val challenge = cand.challengeOpt.get
      cand.copy(children = cand.children.map(_.withChallenge(challenge)))

    case cor: COr2Unproven if cor.challengeOpt.isDefined =>
      ???
      /*
      val rootChallenge = cor.challengeOpt.get
      val challengeSize = rootChallenge.length
      val randomChallenges = cor.children.tail.map(_ => Random.randomBytes(challengeSize))
      val realChallenge = Helpers.xor(rootChallenge +: randomChallenges: _*)
      val childrenChallenges = realChallenge +: randomChallenges
      assert(childrenChallenges.size == cor.children.size)

      cor.copy(children = cor.children.zip(childrenChallenges).map { case (ut, ch) => ut.setChallenge(ch) })*/
  }

  override def normalizeUnprovenTree(unprovenTree: UnprovenTree): UnprovenTree = {
    val t = everywherebu(markSimulated)(unprovenTree).get.asInstanceOf[UnprovenTree]
    everywheretd(challengeDisperse)(t).get.asInstanceOf[UnprovenTree]
  }

  override def prove(unproven: UnprovenTree): ProofT = TreeConversion.proving(secrets)(unproven)
}