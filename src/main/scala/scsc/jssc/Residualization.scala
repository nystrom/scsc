package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

object Residualization {
  import Machine._
  import Continuations._

  def findAccessPath(loc: Loc, σ: Store, ρ: Env): Exp = {
    import scala.collection.mutable.HashSet

    // Bread-first search through the store to find an access path to the location.
    // Doing BFS returns the shortest path.
    var worklist: Vector[(Exp, Loc)] = ρ.toVector map { case (x, v) => (Local(x), v) }
    val seen: HashSet[Loc] = new HashSet()

    while (worklist.nonEmpty) {
      val (path, v) = worklist.head
      worklist = worklist.tail

      if (v == loc) {
        return path
      }
      else if (! seen.contains(loc)) {
        seen += loc

        σ.get(v) match {
          case Some(Closure(loc1: Loc, _)) =>
            worklist = worklist :+ (path, loc1)
          case Some(Closure(FunObject(_, proto, _, _, props), _)) =>
            proto match {
              case loc1: Loc =>
                worklist = worklist :+ (Index(path, StringLit("__proto__")), loc1)
              case _ =>
            }
            props foreach {
              case Property(k, loc1: Loc, _, _) =>
                worklist = worklist :+ (Index(path, k), loc1)
              case _ =>
            }
          case _ =>
        }
      }
    }

    // If there is not an access path, it must be a new object
    // that we haven't stored in a variable yet.

    // If the location stores a value just return it.
    σ.get(loc) match {
      case Some(Closure(_: Loc, _)) =>
        Undefined()
      case Some(Closure(Value(v), _)) =>
        v
      case Some(Closure(FunObject(_, proto, params, Some(e), props), _)) =>
        Lambda(params, e)
      case Some(Closure(FunObject(_, proto, Nil, None, props), _)) =>
        proto match {
          case Prim("Object.prototype") =>
            ObjectLit(props flatMap {
              case Property(k, v, _, _) if k == StringLit("__proto__") =>
                Nil
              case p @ Property(k, v, _, _) =>
                Property(k, reify(v)(σ, ρ), None, None)::Nil
            })
          case Prim("Array.prototype") =>
            val kvs = props flatMap {
              case Property(k, v, _, _) if k == StringLit("__proto__") =>
                Nil
              case p @ Property(StringLit("length"), v, _, _) =>
                Nil
              case p @ Property(CvtNum(n), v, _, _) =>
                (n, reify(v)(σ, ρ))::Nil
            }
            val elements = kvs.sortBy(_._1).map(_._2)
            ArrayLit(elements)
          case v =>
            println(s"PROTOTYPE $v")
            Undefined()
        }
      case _ =>
        // No access path was found.
        Undefined()
    }


  }

  def reify(e: Exp)(implicit σ: Store, ρ: Env): Exp = {
    import scsc.js.TreeWalk._

    object Reify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Residual(e) => super.rewrite(e)
        case e: Loc => findAccessPath(e, σ, ρ)
        case e => super.rewrite(e)
      }
    }

    Reify.rewrite(e) match {
      case Value(e) => e
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

  def strongReify(e: Exp)(implicit σ: Store, ρ: Env): Exp = Residual(unreify(e))

  def strongReifyStore(σ: Store, ρ: Env): Store = σ map {
    case (loc, Closure(v, ρ)) => (loc, Closure(strongReify(v)(σ, ρ), ρ))
  }

  def strongReify(s: St): St = s match {
    case Σ(focus, ρ, σ, ɸ, k) =>
      val focus1 = strongReify(focus)(σ, ρ)
      val vars: Set[Name] = fv(focus1)
      val k1 = vars.toList match {
        case Nil => k
        case vars =>
          val vals = vars map {
            x =>
              ρ.get(x) match {
                case Some(v) => unreify(v)
                case None => Undefined()
              }
          }
          RebuildLet(vars, vals, ρ)::k
      }
      Σ(focus1, ρ, strongReifyStore(σ, ρ), ɸ, k1)
  }
}
