package scsc.jssc

import scsc.js.Trees._

object Machine {
  import Continuations._

  // The state of the CESK machine:
  type St = States.State

  // Inject a term into the machine.
  def inject(e: Exp): St = States.Ev(e, ρ0, σ0, φ0, k0)

  val k0: Cont = Nil

  // TODO: body is not an Exp, but a set of labeled traces.
  // We can have gotos between the traces.
  // At the end we reconstruct the trace.

  // FIXME:
  // the body should not be an exp, but rather a set of labeled traces.
  // Residual(x) is a HANDLE for an effectful expression.
  // We can reconstruct the expression by traversing the body.
  // If all residuals are used linearly in the effect, we just collapse into
  // an expression. Otherwise, we need to introduce assignments.

  // effects should be recreated in the order of the vars.
  case class Effect(vars: List[Name], traces: Map[Name, Exp]) {
    def extend(x: Name, e: Exp): Effect = e match {
      case Undefined() => this
      case e => Effect(vars :+ x, traces + (x -> e))
    }
    def extend(e: Exp): Effect = extend(scsc.util.FreshVar(), e)
    def seq: Exp = seq(Undefined()) match {
      case Seq(s, Undefined()) => s
      case s => s
    }

    def seq(e: Exp): Exp = {
      import scsc.js.TreeWalk._

      object Subst extends Rewriter {
        var used: Set[Name] = Set()

        override def rewrite(e: Exp) = e match {
          case Residual(x) =>
            if (used contains x) {
              Residual(x)
            }
            else {
              traces.get(x) match {
                case Some(e1) =>
                  used += x
                  Assign(None, Residual(x), rewrite(e1))
                case None =>
                  Residual(x)
              }
            }
          case e =>
            super.rewrite(e)
        }
      }

      val xs = vars map { x => Residual(x) }
      (xs :+ e).foldLeft(Undefined(): Exp) {
        case (Undefined(), x) =>
          Subst.rewrite(x)
        case (s, x) =>
          Seq(s, Subst.rewrite(x))
      }
    }

    def exp(x: Name): Exp = seq(Residual(x))
  }

  type Effects = List[Block]
  case class Block(label: Name, vars: List[Name], body: Exp)

  val φ0: Effect = Effect(Nil, Map())

  ////////////////////////////////////////////////////////////////
  // ENVIRONMENTS
  ////////////////////////////////////////////////////////////////

  lazy val ρ0: Env = Context.ρ0
  type Env = Map[Name, Loc]

  // trait Env {
  //   def get(x: Name): Option[Closure]
  //   def add(x: Name, v: Exp, ρ: Env): Env
  //   def addrec(x: Name, v: Exp): Env
  // }
  //
  // val ρ0: Env = MapEnv(Map())
  //
  // case class MapEnv(table: Map[Name, Closure]) extends Env {
  //   override def toString = table.toString
  //
  //   def get(x: Name): Option[Closure] = table.get(x).map {
  //     case Closure(v, SelfEnv) => Closure(v, this)
  //     case Closure(v, ρ) => Closure(v, ρ)
  //   }
  //   def add(x: Name, v: Exp, ρ: Env) = v match {
  //     case v if fv(v).isEmpty => MapEnv(table + (x -> Closure(v, MapEnv(Map()))))
  //     case v => MapEnv(table + (x -> Closure(v, ρ)))
  //   }
  //   def addrec(x: Name, v: Exp) = v match {
  //     case v if fv(v).isEmpty => MapEnv(table + (x -> Closure(v, MapEnv(Map()))))
  //     case v => MapEnv(table + (x -> Closure(v, SelfEnv)))
  //   }
  // }
  //
  // case object SelfEnv extends Env {
  //   override def toString = "self"
  //
  //   def get(x: Name): Option[Closure] = None
  //   def add(x: Name, v: Exp, ρ: Env) = throw new RuntimeException("illegal cycle")
  //   def addrec(x: Name, v: Exp) = throw new RuntimeException("illegal cycle")
  // }

  ////////////////////////////////////////////////////////////////
  // STORES
  ////////////////////////////////////////////////////////////////

  // The store maps locations to closures.

  case class Loc(address: Int)

  import org.bitbucket.inkytonik.kiama.util.Counter

  object FreshLoc extends Counter {
    def apply(): Loc = Loc(next())
  }

  // This is either a function object or a JS object in the heap.
  case class FunObject(typeof: String, proto: Loc, params: List[Name], body: Option[Exp], properties: List[(Name, Loc)])

  sealed trait Closure
  case class ObjClosure(e: FunObject, ρ: Env) extends Closure
  case class ValClosure(e: Val) extends Closure   // literals, prims, residuals
  case class LocClosure(e: Loc) extends Closure
  // represents missing information (the location is legal, but inconsistent)
  case class UnknownClosure() extends Closure

  type Store = Map[Loc, Closure]

  lazy val σ0: Store = Context.σ0

  implicit class StoreOps(σ: Store) {
    def assign(lhs: Loc, rhs: FunObject, ρ: Env): Store = {
      σ + (lhs -> ObjClosure(rhs, ρ))
    }

    def assign(lhs: Path, rhs: FunObject, ρ: Env): Store = {
      assign(Loc(lhs.address), rhs, ρ)
    }

    def assign(lhs: Loc, rhs: Exp, ρ: Env): Store = {
      rhs match {
        case Path(a, p) =>
          σ + (lhs -> LocClosure(Loc(a)))
        case rhs1: Val =>
          σ + (lhs -> ValClosure(rhs1))
        case _ =>
          ???
      }
    }

    def assign(lhs: Path, rhs: Exp, ρ: Env): Store = {
      assign(Loc(lhs.address), rhs, ρ)
    }

    def sanitize(ρ: Env): Store = {
      import scala.collection.mutable.MapBuilder

      val σnew: MapBuilder[Loc, Closure, Store] = new MapBuilder(σ0)

      for ((x, loc) <- ρ) {
        σ.get(loc) match {
          case Some(v) =>
            σnew += (loc -> v)
          case None =>
        }
      }

      σnew.result
    }

    def merge(σ2: Store, ρ: Env): Store = {
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
            case Some(v @ ObjClosure(FunObject(_, proto, _, _, props), _)) =>
              σnew += (loc -> v)
              worklist = worklist :+ proto
              props foreach {
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
  }


}
