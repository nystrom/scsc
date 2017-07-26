package sc.core.machine

trait Stores {
  this: Terms with Envs =>

  type Blob

  sealed trait Loc
  case class HeapLoc(address: Int) extends Loc
  case class StackLoc(address: Int) extends Loc

  implicit object LocOrd extends Ordering[Loc] {
    def compare(a: Loc, b: Loc) = (a, b) match {
      case (StackLoc(_), HeapLoc(_)) => -1
      case (HeapLoc(_), StackLoc(_)) => 1
      case (HeapLoc(a1), HeapLoc(a2)) => a1 - a2
      case (StackLoc(a1), StackLoc(a2)) => a1 - a2
    }
  }

  import org.bitbucket.inkytonik.kiama.util.Counter

  object FreshHeapLoc extends Counter {
    def apply(): HeapLoc = HeapLoc(next())
  }
  object FreshStackLoc extends Counter {
    def apply(): StackLoc = StackLoc(next())
  }

  sealed trait Closure
  case class BlobClosure(e: Blob, ρ: Env) extends Closure
  case class ValueClosure(e: Value) extends Closure {
    require(! e.getClass.getName.endsWith("Path"))
  }
  case class LocClosure(e: HeapLoc) extends Closure
  // represents missing information
  case class UnknownClosure() extends Closure

  import scala.collection.immutable.SortedMap
  type Store = SortedMap[Loc, Closure]

  // Return all heap fields of the blob.
  def scan(b: Blob): List[HeapLoc]

  val σempty: Store = SortedMap()
  val σ0: Store

  def assignValue(σ: Store, lhs: Loc, rhs: Value): Store = {
    σ + (lhs -> ValueClosure(rhs))
  }

  implicit class StoreOps(σ: Store) {
    // Store a simple value in a slot
    def assign(lhs: Loc, rhs: Value): Store = {
      assignValue(σ, lhs, rhs)
    }

    // Store a heap location in a slot
    def assign(lhs: Loc, rhs: HeapLoc): Store = {
      σ + (lhs -> LocClosure(rhs))
    }

    // Store a blob in the heap
    def assign(lhs: HeapLoc, rhs: Blob, ρ: Env): Store = {
      σ + (lhs -> BlobClosure(rhs, ρ))
    }

    // Invalidate all heap locations.
    def invalidateHeap: Store = {
      σ.collect {
        case (loc: StackLoc, v) => (loc, v)
        case (loc: HeapLoc, v) => (loc, UnknownClosure())
      }
    }

    def merge(σ2: Store): Store = {
      val σ1 = σ

      if (σ1 eq σ2) {
        return σ1
      }

      import scala.collection.mutable.MapBuilder

      val σnew: MapBuilder[Loc, Closure, Store] = new MapBuilder(σ0)

      // The paths should be the same.
      // When assigning to a path, need to change all the reachable paths.
      σ1 foreach {
        case (loc1, v1) =>
          σ2.get(loc1) match {
            case Some(v2) if v1 == v2 =>
              σnew += (loc1 -> v2)
            case Some(v2) =>
              σnew += (loc1 -> UnknownClosure())
            case None =>
          }
        }

      σnew.result
    }

/*
    // garbage collect the store with respect to the environment.
    def gc(ρ: Env): Store = {
      import scala.collection.mutable.HashSet
      import scala.collection.mutable.MapBuilder

      var worklist: Vector[Loc] = ρ.toVector map { case (x, v) => v }
      val seen: HashSet[Loc] = new HashSet()
      val σnew: MapBuilder[Loc, Closure, Store] = new MapBuilder(σ0)

      while (worklist.nonEmpty) {
        val loc = worklist.head
        worklist = worklist.tail

        if (! seen.contains(loc)) {
          seen += loc
          σ.get(loc) match {
            case Some(v @ BlobClosure(blob)) =>
              σnew += (loc -> v)
              scan(blob) foreach {
                case (k, loc1) =>
                  worklist = worklist :+ loc1
                case _ =>
              }
            case Some(v @ LocClosure(loc1)) =>
              σnew += (loc -> v)
              worklist = worklist :+ loc1
            case Some(v) =>
              σnew += (loc -> v)
            case None =>
          }
        }
      }

      σnew.result
    }
  */
  }
}
