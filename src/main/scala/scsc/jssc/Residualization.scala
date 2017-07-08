package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

object Residualization {
  import Machine._
  import Continuations._
  import Step._

  def findAccessPath(loc: Loc, σ: Store, ρ: Env): Exp = {
    import scala.collection.mutable.HashSet

    // Bread-first search through the store to find an access path to the location.
    // Doing BFS returns the shortest path.
    var worklist: Vector[(Exp, Loc)] = ρ.toVector map { case (x, v) => (Local(x), v) }
    val seen: HashSet[Loc] = new HashSet()

    while (worklist.nonEmpty) {
      val (path, v) = worklist.head
      worklist = worklist.tail

      println(s"trying path $path to $v for $loc")

      if (v == loc) {
        return path
      }
      else if (! seen.contains(v)) {
        seen += v

        σ.get(v) match {
          case Some(LocClosure(loc1: Loc)) =>
            worklist = worklist :+ (path, loc1)
          case Some(ObjClosure(FunObject(_, proto, _, _, props), _)) =>
            worklist = worklist :+ ((Index(path, StringLit("__proto__")), proto))
            props foreach {
              case (k, loc1: Loc) =>
                worklist = worklist :+ ((Index(path, StringLit(k)), loc1))
              case _ =>
            }
          case _ =>
        }
      }
    }

    // If there is not an access path, it must be a new object
    // that we haven't stored in a variable yet.

    println(s"NO ACCESS PATH found for $loc with σ = $σ and ρ = $ρ")
    Undefined()
  }

  def reify(e: Exp)(implicit σ: Store, ρ: Env): Exp = {
    import scsc.js.TreeWalk._

    object Reify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Residual(e) => super.rewrite(e)
        case Path(_, path) => super.rewrite(path)
        case e => super.rewrite(e)
      }
    }

    val r = Reify.rewrite(e)

    r match {
      case Value(e) => e
      case Residual(e) => Residual(e)
      case e => Residual(e)
    }
  }

  def unreify(e: Exp): Exp = {
    import scsc.js.TreeWalk._

    object Unreify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Residual(e) => super.rewrite(e)
        case e => super.rewrite(e)
      }
    }

    Unreify.rewrite(e)
  }

  def strongReify(e: Exp)(implicit σ: Store, ρ: Env): Exp = Residual(unreify(reify(e)(σ, ρ)))

  def strongReifyStore(σ: Store, ρ: Env): Store = σ map {
    case (loc, ValClosure(v)) => (loc, ValClosure(strongReify(v)(σ, ρ)))
    case (loc, ObjClosure(v, ρ)) => (loc, ObjClosure(v, ρ))
    case (loc, LocClosure(v)) => (loc, LocClosure(v))
    case (loc, UnknownClosure()) => (loc, UnknownClosure())
  }

  def strongReify(s: St): St = s match {
    case Co(focus, σ, φ, k) =>
      val focus1 = strongReify(focus)(σ, Context.ρ0)
      Co(focus1, σ, φ, k)
    case Ev(focus, ρ, σ, φ, k) =>
      val focus1 = strongReify(focus)(σ, ρ)
      Ev(focus1, ρ, σ, φ, k)
  }
}
