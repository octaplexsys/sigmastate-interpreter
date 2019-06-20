package sigmastate.interpreter

import java.math.BigInteger

import sigmastate.UncheckedTree
import sigmastate.Values.SigmaBoolean
import sigmastate.basics.FirstProverMessage

/**
  * A hint for prover, which helps prover to resolve a script. For example, if the script is "pk1 && pk2", and the
  * prover knows only a secret for the public key pk1, the prover fails on proving without a hint. But if the prover
  * knows that pk2 is known to another party, the prover may prove the statement.
  */
trait Hint

/**
  * A hint which is indicating that a secret associated with its public image "image" is known by some other party.
  */
trait OtherSecret extends Hint {
  val image: SigmaBoolean
}

/**
  * A hint which is contains a proof-of-knowledge for a secret associated with its public image "image".
  */
case class OtherSecretProven(override val image: SigmaBoolean, uncheckedTree: UncheckedTree) extends OtherSecret

/**
  * A family of hints which are about a correspondence between a public image of a secret image and prover's commitment
  * to randomness ("a" in a sigma protocol).
  */
trait CommitmentHint extends Hint {
  val image: SigmaBoolean
  val commitment: FirstProverMessage
}

/**
  * A hint which a commitment to randomness associated with a public image of a secret, as well as randomness itself.
  * Please note that this randomness should be kept in secret by the prover.
  *
  * @param image - image of a secret
  * @param randomness - randomness
  * @param commitment - commitment to randomness used while proving knowledge of the secret
  */
case class OwnCommitment(override val image: SigmaBoolean, randomness: BigInteger, commitment: FirstProverMessage) extends CommitmentHint

/**
  * A hint which contains a commitment to randomness associated with a public image of a secret.
  * @param image - image of a secret
  * @param commitment - commitment to randomness used while proving knowledge of the secret
  */
case class OtherCommitment(override val image: SigmaBoolean, commitment: FirstProverMessage) extends OtherSecret with CommitmentHint

/**
  * Collection of hints to be used by a prover
  * @param hints - hints stored in the bag
  */
case class HintsBag(hints: Seq[Hint]) {

  lazy val predefinedCommitments: Seq[OtherCommitment] = hints.filter(_.isInstanceOf[OtherCommitment]).map(_.asInstanceOf[OtherCommitment])

  lazy val otherSecrets: Seq[OtherSecret] = hints.filter(_.isInstanceOf[OtherSecret]).map(_.asInstanceOf[OtherSecret])

  lazy val otherImages = otherSecrets.map(_.image)

  def addHint(hint: Hint): HintsBag = HintsBag(hint +: hints)

  def addHints(newHints: Seq[Hint]): HintsBag = HintsBag(newHints ++ hints)

  def ++(other: HintsBag): HintsBag = HintsBag(other.hints ++ hints)

  lazy val commitments = hints.filter(_.isInstanceOf[CommitmentHint]).map(_.asInstanceOf[CommitmentHint])
  lazy val proofs = hints.filter(_.isInstanceOf[OtherSecretProven]).map(_.asInstanceOf[OtherSecretProven])

  override def toString: String = s"Hints(${hints.mkString("\n")})"
}

object HintsBag {
  val empty = HintsBag(Seq())
}