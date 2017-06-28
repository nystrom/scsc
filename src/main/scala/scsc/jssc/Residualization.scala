package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

object Residualization {
  import Machine._
  import Continuations._

  def reify(e: Exp): Exp = e match {
    case e @ Num(n) => e
    case e @ Bool(n) => e
    case e @ StringLit(n) => e
    case e @ ArrayLit(es) if es.forall(e => e == reify(e)) => e
    case e @ ObjectLit(es) if es.forall(e => e == reify(e)) => e
    case e @ Property(k, v, None, None) if k == reify(k) && v == reify(v) => e
    case e @ Lambda(_, _) => unreify(e)
    case e @ Loc(_) => ???  // cannot reify a location
    case e @ Residual(e1) => reify(e1)
    case e => strongReify(e)
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

  def strongReify(e: Exp): Exp = Residual(unreify(e))

  def strongReifyEnv(ρ: Env): Env = ρ

  def strongReifyStore(σ: Store): Store = σ map {
    case (loc, Closure(v, ρ)) => (loc, Closure(strongReify(v), strongReifyEnv(ρ)))
  }

  def strongReify(s: St): St = s match {
    case Σ(focus, ρ, σ, k) =>
      val vars: Set[Name] = fv(focus)
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
      Σ(strongReify(focus), strongReifyEnv(ρ), strongReifyStore(σ), k1)
  }
}
