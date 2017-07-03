package scsc.jssc

import scsc.js.Trees._

object Machine {
  import Continuations._

  // The state of the CESFK machine:
  case class Σ(c: Exp, e: Env, s: Store, f: Effect, k: Cont) {
    override def toString = s"Σ(e = ${c.show}, ρ = $e, σ = $s, ɸ = $f, k = $k)"
  }

  type St = Σ

  // Inject a term into the machine.
  def inject(e: Exp): St = Σ(e, ρ0, σ0, ɸ0, Nil)

  ////////////////////////////////////////////////////////////////
  // EFFECTS
  ////////////////////////////////////////////////////////////////

  type Effect = Exp
  lazy val ɸ0 = Undefined()

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

  // The heap stores closures.
  case class Closure(e: Exp, ρ: Env)

  type Store = Map[Loc, Closure]

  lazy val σ0: Store = Context.σ0

  implicit class StoreOps(σ: Store) {
    def assign(lhs: Loc, rhs: Exp, ρ: Env) = {
      σ + (lhs -> Closure(rhs, ρ))
    }

    def sanitize: Store = σ

    def merge(σ2: Store): Store = {
      val σ1 = σ

      if (σ1 eq σ2) {
        return σ1
      }

      import scala.collection.mutable.MapBuilder

      val σnew: MapBuilder[Loc, Closure, Store] = new MapBuilder(σ0)

      for ((loc1, v1) <- σ1) {
        σ2.get(loc1) match {
          case Some(v2) if v1 == v2 =>
            σnew += (loc1 -> v2)
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
            case Some(v @ Closure(FunObject(_, proto, _, _, props), _)) =>
              σnew += (loc -> v)
              proto match {
                case loc1: Loc =>
                  worklist = worklist :+ loc1
              }
              props foreach {
                case Property(k, loc1: Loc, _, _) =>
                  worklist = worklist :+ loc1
                case _ =>
              }
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
