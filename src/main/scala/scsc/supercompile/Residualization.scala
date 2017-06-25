package scsc.supercompile

import scala.collection.mutable.ListBuffer
import scsc.syntax.LambdaSyntax._
import scsc.syntax.Trees._
import scsc.syntax.FreeVars._

object Residualization {
  import Machine._

  def reify(e: Exp): Exp = e match {
    case Num(n) => Num(n)
    case Lam(x, e) => Lam(x, unreify(e))
    case Ctor(k, es) if e.costZero && fv(e).isEmpty => e
    case Residual(e) => reify(e)
    case Var(x) => Residual(Var(x))
    case App(e1, e2) => Residual(App(unreify(e1), unreify(e2)))
    case Bin(op, e1, e2) => Residual(Bin(op, unreify(e1), unreify(e2)))
    case Neg(e) => Residual(Neg(unreify(e)))
    case Not(e) => Residual(Not(unreify(e)))
    case Ctor(k, es) => Residual(Ctor(k, es.map(unreify)))
    case Let(x, e1, e2) => Residual(Let(x, unreify(e1), unreify(e2)))
    case Letrec(x, e1, e2) => Residual(Letrec(x, unreify(e1), unreify(e2)))
    case Case(e, alts) => Residual(Case(unreify(e), alts.map { case Alt(p, e) => Alt(p, unreify(e)) }))
  }

  def strongReify(e: Exp): Exp = Residual(unreify(e))

  def unreify(e: Exp): Exp = e match {
    case Num(n) => Num(n)
    case Lam(x, e) => Lam(x, unreify(e))
    case Residual(e) => unreify(e)
    case Var(x) => Var(x)
    case App(e1, e2) => App(unreify(e1), unreify(e2))
    case Bin(op, e1, e2) => Bin(op, unreify(e1), unreify(e2))
    case Neg(e) => Neg(unreify(e))
    case Not(e) => Not(unreify(e))
    case Ctor(k, es) => Ctor(k, es.map(unreify))
    case Let(x, e1, e2) => Let(x, unreify(e1), unreify(e2))
    case Letrec(x, e1, e2) => Letrec(x, unreify(e1), unreify(e2))
    case Case(e, alts) => Case(unreify(e), alts.map { case Alt(p, e) => Alt(p, unreify(e)) })
  }

  def strongReify(ρ: Env): Env = ρ match {
    case MapEnv(m) => MapEnv(m.map {
      case (x, Closure(e, ρ)) => (x, Closure(strongReify(e), strongReify(ρ)))
    })
    case SelfEnv => SelfEnv
  }

  def strongReify(s: St): St = s match {
    case Σ(focus, ρ, σ, k) =>
      val vars = fv(focus)
      // val vars = focus match { case Var(x) => Set(x) ; case _ => Set() }
      val k1 = vars.toList.foldLeft(k) {
        case (k, x) =>
          ρ.get(x) match {
            case Some(Closure(v, ρ)) =>
              RebuildLet(x, unreify(v), ρ, k)
            case None =>
              k
          }
      }
      Σ(strongReify(focus), strongReify(ρ), σ, k1)
  }
}
