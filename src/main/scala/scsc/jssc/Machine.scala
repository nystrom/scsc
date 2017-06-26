package scsc.jssc

import scsc.js.Trees._

object Machine {
  import Continuations._

  // The state of the CEK machine:
  case class Σ(c: Exp, e: Env, s: Store, k: Cont) {
    override def toString = s"Σ(e = ${c.show}, ρ = $e, σ = $s, k = $k)"
  }

  type St = Σ

  // Inject a term into the machine.
  def inject(e: Exp): St = Σ(e, ρ0, σ0, Nil)

  ////////////////////////////////////////////////////////////////
  // ENVIRONMENTS
  ////////////////////////////////////////////////////////////////

  // In the CESK machine, environments map names to values (locations)
  // and the store maps locations to closures.
  case class Closure(e: Exp, ρ: Env) {
    override def toString = s"Closure(${e.show}, $ρ)"
  }

  val ρ0: Env = Map()
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

  type Store = Map[Loc, Closure]

  implicit class StoreOps(σ: Store) {
    def assign(lhs: Loc, rhs: Exp, ρ: Env) = {
      σ + (lhs -> Closure(rhs, ρ))
    }
  }

  val σ0: Store = Map()

  def mergeStores(σ1: Store, σ2: Store): Store = {
    if (σ1 eq σ2) {
      return σ1
    }

    import scala.collection.mutable.MapBuilder
    val σnew: MapBuilder[Loc, Closure, Store] = new MapBuilder(σ0)
    for ((loc1, v1) <- σ1) {
      σ2.get(loc1) match {
        case Some(v2) if v1 == v2 =>
          σnew += ((loc1, v2))
        case None =>
      }
    }
    σnew.result
  }

}
