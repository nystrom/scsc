package scsc.supercompile

import scsc.syntax.LambdaSyntax._
import scsc.syntax.Trees._
import scsc.syntax.FreeVars._

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

  // In the CEK machine, environments map to closures.

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
  sealed trait Cont extends Product
  case object Done extends Cont {
    override def toString = "∅"
  }
  case class EvalArg(arg: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"☐ ${arg.show} then $k"
  }
  case class Call(funValue: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"${funValue.show} ☐ then $k"
  }
  case class Fail(s: String) extends Cont {
    override def toString = s"FAIL($s)"
  }

  // Extensions:
  // Binary operators.
  case class OpRight(op: Operator, e2: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"☐ $op ${e2.show} then $k"
  }
  case class EvalOp(op: Operator, v1: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"${v1.show} $op ☐ then $k"
  }

  // Constructors.
  case class EvalCtorArgs(n: Name, argsToCompute: List[Exp], argsComputed: List[Exp], ρ: Env, k: Cont) extends Cont {
    override def toString = s"($n ${argsComputed.map(_.show).reverse.mkString(" ")} ☐ ${argsToCompute.map(_.show).mkString(" ")}) then $k"
  }

  // Let
  case class LetCont(x: Name, e: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"(let $x = ☐ in ${e.show}) then $k"
  }

  // Let
  case class LetrecCont(x: Name, e: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"(letrec $x = ☐ in ${e.show}) then $k"
  }

  // Case expressions
  case class EvalCase(alts: List[Alt], ρ: Env, k: Cont) extends Cont {
    override def toString = s"(case ☐ of ${alts.map(_.show).mkString(" | ")}) then $k"
  }
  case class EvalAlts(alts: List[Alt], ρ: Env, k: Cont) extends Cont {
    override def toString = s"(case ☐ of ${alts.map(_.show).mkString(" | ")}) then $k"
  }

  // Reificiation
  case class RebuildLet(x: Name, e: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"«let $x = ${e.show} in ☐» then $k"
  }
  case class RebuildLetrec(x: Name, e: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"«letrec $x = ${e.show} in ☐» then $k"
  }
  case class RebuildCase(alts: List[Alt], altsPrime: List[Alt], ρ: Env, σOpt: Option[Store], k: Cont) extends Cont {
    override def toString = s"«case ☐ of ${(altsPrime.reverse ++ alts).map(_.show).mkString(" | ")}» then $k"
  }
  case class RebuildAlt(e: Exp, p: Pat, alts: List[Alt], altsPrime: List[Alt], ρ: Env, k: Cont) extends Cont {
    override def toString = (alts, altsPrime) match {
      case (Nil, Nil) =>
        s"«case ${e.show} of $p -> ☐» then $k"
      case (alts, Nil) =>
        s"«case ${e.show} of $p -> ☐ | ${alts.map(_.show).mkString(" | ")}» then $k"
      case (Nil, altsPrime) =>
        s"«case ${e.show} of ${altsPrime.reverse.map(_.show).mkString(" | ")} | $p -> ☐» then $k"
      case (alts, altsPrime) =>
        s"«case ${e.show} of ${altsPrime.reverse.map(_.show).mkString(" | ")} | $p -> ☐ | ${alts.map(_.show).mkString(" | ")}» then $k"
    }
  }

}
