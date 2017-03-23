package scsc.supercompile

import scala.collection.mutable.ListBuffer
import scsc.syntax.LambdaSyntax._
import scsc.syntax.Trees._
import scsc.syntax.FreeVars._

// We start with a CEK machine for the lambda calculus.
object HE {
  import scsc.supercompile.Machine._
  import scsc.supercompile.Residualization._
  import scsc.supercompile.CEK._

  // In SC / PE, we get stuck when focus is a Var!
  // Add continuations for Bin and for Case, etc.

  // PE builds the residual directly.
  // In PE, when we get "stuck", we recurse on subexpressions.
  // Can we *add* residualization to the continuation...
  // e.g., when doing x+2
  // we get to the configuration: (x, [], OpRight(+, 2, k))
  // then we go to the configuration: (2, [], EvalOp(+, x, k))
  // then we want to eval x+2, but we can't so we make a "value" for x+2
  // to avoid repeating we do Residual(x+2).
  // We do this rather than splitting?

  // To convert to a term just reify the focus and run the machine to termination.
  def toTerm(s: St): Option[(Exp, Int)] = {
    println("converting to term " + s)
    s match {
      case Σ(e, ρ, σ, Done) =>
        val u = unreify(e)
        println("--> " + u)
        Some((u, 0))
      case Σ(e, ρ, σ, Fail(_)) =>
        None
      case Σ(e, ρ, σ, k) =>
        val s1 = step(Σ(strongReify(e), ρ, σ, k))
        toTerm(s1) map {
          case (u, n) => (u, n+1)
        }
    }
  }

  type FoldResult = (Name, Exp, Exp, Exp)

  def tryFold(s: St, target: St): Option[FoldResult] = {
    (toTerm(s), toTerm(target)) match {
      case (Some((e1, _)), Some((e2, _))) =>
        tryFoldExp(e1, e2) match {
          case Some(u) => return Some(u)
          case None =>
        }
      case _ =>
    }

    target match {
      case Σ(e, ρ, σ, Done) =>
        tryFoldStVsExp(s, e)
      case Σ(e, ρ, σ, Fail(_)) =>
        None
      case Σ(e, ρ, σ, k: RebuildCont) =>
        tryFoldStVsExp(s, e) match {
          case Some(u) =>
            println("--> " + u)
            Some(u)
          case None =>
            val target1 = step(Σ(strongReify(e), ρ, σ, k))
            tryFold(s, target1)
        }
      case Σ(e, ρ, σ, k) =>
        val target1 = step(Σ(strongReify(e), ρ, σ, k))
        tryFold(s, target1)
    }
  }

  def tryFoldStVsExp(s: St, target: Exp): Option[FoldResult] = {
    s match {
      case Σ(e, ρ, σ, Done) =>
        tryFoldExp(e, target)
      case Σ(e, ρ, σ, Fail(_)) =>
        None
      case Σ(e, ρ, σ, k: RebuildCont) =>
        tryFoldExp(e, target) match {
          case Some(u) =>
            println(s"    ---> ${u}")
            Some(u)
          case None =>
            val s1 = step(Σ(strongReify(e), ρ, σ, k))
            tryFoldStVsExp(s1, target)
        }
      case Σ(e, ρ, σ, k) =>
        val s1 = step(Σ(strongReify(e), ρ, σ, k))
        tryFoldStVsExp(s1, target)
    }
  }

  def tryFoldExp(e1: Exp, e2: Exp): Option[FoldResult] = {
    val u1 = unreify(e1)
    val u2 = unreify(e2)

    // u1 match {
    //   case Var(_) => return None
    //   case v if v.isValue => return None
    //   case _ =>
    // }
    //
    // u2 match {
    //   case Var(_) => return None
    //   case v if v.isValue => return None
    //   case _ =>
    // }

    println(s"TRY FOLD ${u1.show}")
    println(s"      vs ${u2.show}")
    MSG.msgTerms(u1, u2)
  }

  def size(e: Exp): Int = e match {
    case App(e1, e2) => size(e1) + size(e2) + 1
    case Bin(_, e1, e2) => size(e1) + size(e2) + 1
    case Neg(e) => size(e) + 1
    case Not(e) => size(e) + 1
    case Ctor(k, es) => es.map(size(_)).sum + 1
    case Let(x, e1, e2) => size(e1) + size(e2) + 1
    case Letrec(x, e1, e2) => size(e1) + size(e2) + 1
    case Case(e, alts) => size(e) + alts.map { case Alt(p, e) => size(e) }.sum + 1
    case Lam(x, e) => size(e) + 1
    case Var(_) => 1
    case Num(v) => v.abs.toInt
    case Residual(e) => size(e)
  }

  // Homeomorphic embedding code
  implicit class ExpHE(e1: Exp) {
    def <<|(e2: Exp): Boolean = {
      size(e1) <= size(e2) && he(e1, e2)
    }

    def he(e1: Exp, e2: Exp) = diving(e1, e2) || coupling(e1, e2)

    def diving(t1: Exp, t2: Exp): Boolean = t2 match {
      case App(e1, e2) => he(t1, e1) || he(t1, e2)
      case Bin(_, e1, e2) => he(t1, e1) || he(t1, e2)
      case Neg(e) => he(t1, e)
      case Not(e) => he(t1, e)
      case Ctor(k, es) => es.exists(he(t1, _))
      case Let(x, e1, e2) => he(t1, e1) || he(t1, e2)
      case Letrec(x, e1, e2) => he(t1, e1) || he(t1, e2)
      case Case(e, alts) => he(t1, e) || alts.exists { case Alt(p, e) => he(t1, e) }
      case Lam(x, e) => he(t1, e)
      case Var(_) => false
      case Num(_) => false
      case Residual(e) => he(t1, e)
    }

    def coupling(t1: Exp, t2: Exp): Boolean = (t1, t2) match {
      case (Var(_), Var(_)) => true
      case (App(f1, a1), App(f2, a2)) => he(f1, f2) && he(a1, a2)
      case (Bin(op1, f1, a1), Bin(op2, f2, a2)) => op1 == op2 && he(f1, f2) && he(a1, a2)
      case (Not(a1), Not(a2)) => he(a1, a2)
      case (Neg(a1), Neg(a2)) => he(a1, a2)
      case (Ctor(k1, es1), Ctor(k2, es2)) => k1 == k2 && es1.length == es2.length && (es1 zip es2).forall { case (e1, e2) => he(e1, e2) }
      case (Lam(x1, e1), Lam(x2, e2)) => he(e1, e2)
      case (Let(x1, e1, f1), Let(x2, e2, f2)) => he(e1, e2) && he(f1, f2)
      case (Letrec(x1, e1, f1), Letrec(x2, e2, f2)) => he(e1, e2) && he(f1, f2)
      case (Case(e1, alts1), Case(e2, alts2)) =>
        he(e1, e2) && alts1.length == alts2.length && (alts1 zip alts2).forall {
          case (Alt(p1, e1), Alt(p2, e2)) => he(e1, e2)
        }

      // Treat numbers specially.
      // We compare numbers for equality when they're small.
      // Otherwise, we say just return true.
      // This ensures we eventually stop if the numbers grow without
      // bound and nothing else changes.
      case (Num(k1), Num(k2)) => k1 == k2 || k1.abs > 1000 || k2.abs > 1000

      case (e1, Residual(e2)) => coupling(e1, e2)
      case (Residual(e1), e2) => coupling(e1, e2)

      case _ => false
    }
  }

  implicit class StHE(s1: St) {
    def <<|(s2: St): Boolean = (s1, s2) match {
      // Only compare states if the focus expression is the same and the first continuation
      // is of the same type. That is, we're evaluatnig the same expression in
      // a similar context.
      // Otherwise, we might have too many false positives.
      //
      // FIXME: currently the whistle blows a bit too often.
      // For instance, with the logarithmic version of pow.
      // Need to incorporate the environment too, perhaps.
      case (s1 @ Σ(e1, ρ1, σ1, k1), s2 @ Σ(e2, ρ2, σ2, k2)) if e1 == e2 && k1.getClass == k2.getClass =>
        (toTerm(s1), toTerm(s2)) match {
          case (Some((t1, n1)), Some((t2, n2))) =>
            println("HE: comparing " + s1)
            println("           vs " + s2)
            println("HE:     terms " + t1.show)
            println("           vs " + t2.show)
            println("HE:     sizes " + size(t1))
            println("           vs " + size(t2))
            println("HE:     steps " + n1)
            println("           vs " + n2)

            n1 <= n2 && t1 <<| t2
          case (None, None) => true  // if both fail, blow the whistle!
          case _ => false
        }
      case _ => false
    }
  }

  // termination:
  // a precondition of nontermination is that values grow.
  // but this is difficult to implement here because we have numbers (which "change" not "grow")
  //
  // Homeomorphic embedding says a previous state is a subsequence of the new state.
  // HE works well with terms.
  // tagbags are an approximation: a well-quasi order
  //
  // states are more complicated.
  // simple test.... if we run ahead 1000 steps, do we terminate?
  // if yes, ok.
  // if not, then, we can either just run ahead 1000 steps or we can generalize the two states
  // in the history
  // So, don't bother with the HE or anything like that.
  // This may actually work very well in practice because we won't PE code forever

  // Continuation generalization.
  // We fold two states that have the same focus and different continuations.
  // (e, k1) fold (e, k2)
  // where k1 = k1' ++ k
  //       k2 = k2' ++ k
  // we generalize k1' and k2' to k', getting k' ++ k
  // then we restart in (e, k' ++ k)
}
