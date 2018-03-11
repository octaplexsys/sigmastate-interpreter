package sigmastate.serialization

import sigmastate.SType.TypeCode
import sigmastate._
import sigmastate.Values._
import sigmastate.serialization.ValueSerializer.Position

case class RelationSerializer[S1 <: SType, S2 <: SType, R <: Relation[S1, S2]]
  (override val opCode: Byte,
   constructor: (Value[S1], Value[S2]) => R,
   constraints: Seq[Constraints.Constraint2]) extends ValueSerializer[R] {

  import ValueSerializer.{serialize, deserialize}

  val typeCode: TypeCode = SBoolean.typeCode

  override def parseBody(bytes: Array[Byte], pos: Position) = {
    val (firstArg, consumed) = deserialize(bytes, pos)
    val (secondArg, consumed2) = deserialize(bytes, pos + consumed)
    assert(constraints.forall(c => c(firstArg.tpe.typeCode, secondArg.tpe.typeCode)))
    (constructor(firstArg.asInstanceOf[Value[S1]], secondArg.asInstanceOf[Value[S2]]),
      (consumed + consumed2))
  }

  override def serializeBody(rel: R) = {
    serialize(rel.left) ++ serialize(rel.right)
  }
}