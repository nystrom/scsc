package sc.imp.machine

import sc.core.machine

trait Stores extends machine.Stores {
  this: Terms with Envs =>

  // A blob is a structure in the store.
  // A blob should not be used directly as a value.
  trait Blob

  val NullLoc: HeapLoc = FreshHeapLoc()

  // A stack frame
  case class StackFrameBlob(outer: HeapLoc, slots: List[(Name, HeapLoc)]) extends Blob

  case class ObjectBlob(props: List[(Name, HeapLoc)]) extends Blob
  case class ArrayBlob(props: List[(Int, HeapLoc)]) extends Blob
  case class LambdaBlob(e: Lambda) extends Blob

  def scan(blob: Blob) = blob match {
    case StackFrameBlob(outer, slots) => outer :: slots.sortBy(_._1).map(_._2)
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
