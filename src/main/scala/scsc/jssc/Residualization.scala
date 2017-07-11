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
        case Path(_, path) => super.rewrite(path)
        case e => super.rewrite(e)
      }
    }

    Reify.rewrite(e)
  }

  def unreify(e: Exp): Exp = {
    import scsc.js.TreeWalk._

    object Unreify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Residual(x) => Local(x)
        case e => super.rewrite(e)
      }
    }

    Unreify.rewrite(e)
  }

  def strongReify(s: St): St = s match {
    case Co(focus, σ, φ, k) =>
      Co(focus, σ, φ, k)
    case Ev(focus, ρ, σ, φ, k) =>
      Co(Undefined(), σ, φ, k).MakeResidual(focus, ρ, k)
    case s =>
      s
  }

  // To convert to a term, we run the machine until it terminates, reifying
  // the focus each step.
  def toTerm(s: St): Option[(Val, Effect, Int)] = {
    toTermAcc(s, 0)
  }

  @scala.annotation.tailrec
  def toTermAcc(s: St, steps: Int): Option[(Val, Effect, Int)] = {
    println("converting to term " + s)
    s match {
      case s @ Halt(e, σ, φ) =>
        val t = s.residual
        println("--> " + t)
        Some((e, φ, steps))

      case Err(_, _) =>
        None

      case s0 =>
        val s1 = strongReify(s0)
        val s2 = s1.step
        toTermAcc(s2, steps+1)
    }
  }
}
