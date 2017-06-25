package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

object Residualization {
  import Machine._

  def reify(e: Exp): Exp = e match {
    case e @ Num(n) => e
    case e @ Bool(n) => e
    case e @ StringLit(n) => e
    case e @ ArrayLit(es) if es.forall(e => e == reify(e)) => e
    case e @ ObjectLit(es) if es.forall(e => e == reify(e)) => e
    case e @ Property(k, v) if k == reify(k) && v == reify(v) => e
    case e @ Lambda(_, _) => unreify(e)
    case     Residual(e) => reify(e)
    case e => strongReify(e)
  }

  def strongReify(e: Exp): Exp = Residual(unreify(e))

  def unreify(e: Exp): Exp = e

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
