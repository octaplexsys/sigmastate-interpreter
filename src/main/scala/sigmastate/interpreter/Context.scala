package sigmastate.interpreter

import sigmastate.SType
import sigmastate.Values.EvaluatedValue

/**
  * Variables to be put into context
  */
case class ContextExtension(values: Map[Byte, EvaluatedValue[_ <: SType]])


trait Context[C <: Context[C]] {
  val extension: ContextExtension

  def withExtension(newExtension: ContextExtension): C
}
