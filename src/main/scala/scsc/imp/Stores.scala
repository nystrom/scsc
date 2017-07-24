package scsc.imp

import scsc.machine

trait Stores extends machine.Stores {
  type MachineType <: Machine { type StoresType = Stores.this.type }

  trait Blob

  import machine._
  import machine.terms._

  case class ObjectBlob(props: List[(Name, HeapLoc)]) extends Blob
  case class ArrayBlob(props: List[(Int, HeapLoc)]) extends Blob
  case class LambdaBlob(e: Lambda) extends Blob

  def scan(blob: Blob) = blob match {
    case ObjectBlob(props) => props.sortBy(_._1).map(_._2)
    case ArrayBlob(props) => props.sortBy(_._1).map(_._2)
    case _ => Nil
  }

  // override to ensure Paths and Pairs are not added to the store
  // A better fix is to not make Paths values.
  override def assignValue(σ: Store, lhs: Loc, rhs: Value): Store = {
    rhs match {
      case Path(v: HeapLoc, _) =>
        σ.assign(lhs, v)
      case Path(_: StackLoc, _) =>
        assert(false, s"cannot add stack location $rhs to the heap")
        σ
      case PairValue(_, _) =>
        assert(false, s"cannot add pair $rhs to the heap value")
        σ
      case v =>
        super.assignValue(σ, lhs, v)
    }
  }
}
