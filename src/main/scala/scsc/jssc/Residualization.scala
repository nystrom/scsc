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

  def reify(e: Exp): Exp = {
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

  def strongReify(e: Exp): (Exp, Effect) = {
    reify(e) match {
      case v @ Residual(e) =>
        val x = scsc.util.FreshVar()
        (Residual(Local(x)), Assign(None, LocalAddr(x), e)::Nil)
      case v =>
        (Residual(v), Nil)
    }
  }

  def strongReify(s: St): St = s match {
    case Co(focus, σ, φ, k) =>
      val (focus1, φ1) = strongReify(focus)
      Co(focus1, σ, φ ++ φ1, k)
    case Ev(focus, ρ, σ, φ, k) =>
      val (focus1, φ1) = strongReify(focus)
      Ev(focus1, ρ, σ, φ ++ φ1, k)
    case s =>
      s
  }
}
