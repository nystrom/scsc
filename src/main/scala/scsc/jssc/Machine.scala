package scsc.jssc

import scsc.js.Trees._

object Machine {

  // The state of the CEK machine:
  case class Σ(c: Exp, e: Env, s: Store, k: Cont) {
    override def toString = s"Σ(e = ${c.show}, ρ = $e, σ = $s, k = $k)"
  }

  type St = Σ

  // Inject a term into the machine.
  def inject(e: Exp): St = Σ(e, ρ0, σ0, Done)

  ////////////////////////////////////////////////////////////////
  // ENVIRONMENTS
  ////////////////////////////////////////////////////////////////

  // In the CESK machine, environments map names to values (locations)
  // and the store maps locations to closures.
  case class Closure(e: Exp, ρ: Env) {
    override def toString = s"Closure(${e.show}, $ρ)"
  }

  val ρ0: Env = MapEnv(Map())

  trait Env {
    def get(x: Name): Option[Closure]
    def add(x: Name, v: Exp, ρ: Env): Env
    def addrec(x: Name, v: Exp): Env
  }

  case class MapEnv(table: Map[Name, Closure]) extends Env {
    override def toString = table.toString

    def get(x: Name): Option[Closure] = table.get(x).map {
      case Closure(v, SelfEnv) => Closure(v, this)
      case Closure(v, ρ) => Closure(v, ρ)
    }
    def add(x: Name, v: Exp, ρ: Env) = v match {
      case v if fv(v).isEmpty => MapEnv(table + (x -> Closure(v, MapEnv(Map()))))
      case v => MapEnv(table + (x -> Closure(v, ρ)))
    }
    def addrec(x: Name, v: Exp) = v match {
      case v if fv(v).isEmpty => MapEnv(table + (x -> Closure(v, MapEnv(Map()))))
      case v => MapEnv(table + (x -> Closure(v, SelfEnv)))
    }
  }

  case object SelfEnv extends Env {
    override def toString = "self"

    def get(x: Name): Option[Closure] = None
    def add(x: Name, v: Exp, ρ: Env) = throw new RuntimeException("illegal cycle")
    def addrec(x: Name, v: Exp) = throw new RuntimeException("illegal cycle")
  }

  ////////////////////////////////////////////////////////////////
  // STORES
  ////////////////////////////////////////////////////////////////

  type Loc = Int
  type Store = Map[Loc, Closure]

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

  ////////////////////////////////////////////////////////////////
  // CONTINUATIONS
  ////////////////////////////////////////////////////////////////

  // Here are the standard CEK continuations + a failure continuation
  sealed trait Cont extends Product {
    def next: Cont
  }

  case object Done extends Cont {
    override def toString = "∅"
    override def next = this
  }

  case class EvalArg(arg: Exp, ρ: Env, next: Cont) extends Cont {
    override def toString = s"☐ ${arg.show} then $next"
  }
  case class DoCall(funValue: Exp, ρ: Env, next: Cont) extends Cont {
    override def toString = s"${funValue.show} ☐ then $next"
  }
  case class Fail(s: String) extends Cont {
    override def toString = s"FAIL($s)"
    override def next = this
  }

  // Extensions:

  // Unary operators
  case class UnaryCont(op: Operator, ρ: Env, next: Cont) extends Cont {
    override def toString = s"$op ☐ then $next"
  }

  // Binary operators.
  case class OpRight(op: Operator, e2: Exp, ρ: Env, next: Cont) extends Cont {
    override def toString = s"☐ $op ${e2.show} then $next"
  }
  case class EvalOp(op: Operator, v1: Exp, ρ: Env, next: Cont) extends Cont {
    override def toString = s"${v1.show} $op ☐ then $next"
  }

  case class BindCont(x: Name, ρ: Env, next: Cont) extends Cont
  case class BlockCont(ss: List[Exp], ρ: Env, next: Cont) extends Cont
  case class BranchCont(t: Cont, f: Cont, next: Cont) extends Cont
  case class LoopCont(label: Option[Name], cont: Cont, brk: Cont) extends Cont {
    override def next = brk
  }

  // Constructors.
  case class EvalCtorArgs(n: Name, argsToCompute: List[Exp], argsComputed: List[Exp], ρ: Env, next: Cont) extends Cont {
    override def toString = s"($n ${argsComputed.map(_.show).reverse.mkString(" ")} ☐ ${argsToCompute.map(_.show).mkString(" ")}) then $next"
  }

  sealed trait RebuildCont extends Cont

  case class RebuildLet(x: Name, v: Exp, ρ: Env, next: Cont) extends RebuildCont {
    override def toString = s"[[ let $x = $v in ☐ ]] then $next"
  }
}
