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
    case e @ Property(k, Some(v), None, None) if k == reify(k) && v == reify(v) => e
    case e @ Property(k, None, None, None) if k == reify(k) => e
    case e @ Lambda(_, _) => unreify(e)
    case e @ Residual(e1) => reify(e1)
    case e => strongReify(e)
  }

  def strongReify(e: Exp): Exp = Residual(unreify(e))

  def unreify(e: Exp): Exp = {
    import scsc.js.TreeWalk._

    object Unreify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Residual(e) => e
        case e => e
      }
    }

    Unreify.rewrite(e)
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
