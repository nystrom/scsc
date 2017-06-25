package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

// We start with a CEK machine for the lambda calculus.
object HE {
  import Machine._
  import Residualization._
  import CEK._

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
  def toTerm(s: St): Option[(Node, Int)] = {
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

  def tryFold(s: St, target: St): Option[FoldResult] = None

/*
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
  */

  def size(e: Node): Int = {
    import scsc.js.TreeWalk._

    object Sizer {
      var size = 0

      def rewrite(e: Exp) = e match {
        case Num(n) if n.abs < 100 =>
          size += n.abs.toInt
        case Num(n) =>
          size += 101
        case e =>
          size += 1
      }
    }

    Sizer.rewrite(e)
    Sizer.size
  }

  // Homeomorphic embedding code
  implicit class ExpHE(e1: Exp) {
    def <<|(e2: Exp): Boolean = {
      size(e1) <= size(e2) && he(e1, e2)
    }

    def he(e1: Exp, e2: Exp) = diving(e1, e2) || coupling(e1, e2)

    def diving(t1: Exp, t2: Exp): Boolean = {
      import scsc.js.TreeWalk._

      object Diver extends Rewriter {
        var yes = false

        override def rewrite(e: Exp) = e match {
          case Break(_) | Continue(_) => e
          case Empty() => e
          case Ident(_) => e
          case Return(None) | Yield(None) => e
          case LetDef(_, None) | ConstDef(_, None) | VarDef(_, None) => e
          case e =>
            if (yes || he(t1, e)) {
              e
            }
            else {
              super.rewrite(e)
            }
        }
      }

      Diver.rewrite(t2)
      Diver.yes
    }

    def divingOld(t1: Exp, t2: Exp): Boolean = t2 match {
      case Unary(_, e) => he(t1, e)
      case IncDec(_, e) => he(t1, e)
      case Delete(e) => he(t1, e)
      case New(e) => he(t1, e)
      case Typeof(e) => he(t1, e)
      case Void(e) => he(t1, e)
      case Assign(_, e1, e2) => he(t1, e1) || he(t1, e2)
      case Binary(_, e1, e2) => he(t1, e1) || he(t1, e2)
      case Access(e, x) => he(t1, e)
      case Block(es) => es.exists(he(t1, _))
      case Break(_) => false
      case Continue(_) => false
      case Call(e, es) => he(t1, e) || es.exists(he(t1, _))
      case Case(e1, e2) => he(t1, e1) || he(t1, e2)
      case Catch(e1, e2, e3) => he(t1, e1) || he(t1, e2) || he(t1, e3)
      case Empty() => false
      case Eval(e) => he(t1, e)
      case For(e1, e2, e3, e4) => he(t1, e1) || he(t1, e2) || he(t1, e3) || he(t1, e4)
      case FunDef(n, xs, e) => he(t1, e)
      case Lambda(xs, e) => he(t1, e)
      case Ident(_) => false
      case Index(e1, e2) => he(t1, e1) || he(t1, e2)
      case Label(_, e) => he(t1, e)
      case ArrayLit(es) => es.exists(he(t1, _))
      case ObjectLit(es) => es.exists(he(t1, _))
      case Property(k, v) => he(t1, k) || he(t1, v)
      case Return(Some(e)) => he(t1, e)
      case Yield(Some(e)) => he(t1, e)
      case Return(None) => false
      case Yield(None) => false
      case Switch(e, es) => he(t1, e) || es.exists(he(t1, _))
      case Cond(e0, e1, e2) => he(t1, e0) || he(t1, e1) || he(t1, e2)
      case Try(e0, es, Some(e2)) => he(t1, e0) || es.exists(he(t1, _)) || he(t1, e2)
      case Try(e0, es, None) => he(t1, e0) || es.exists(he(t1, _))
      case Throw(e) => he(t1, e)
      case VarDef(x, Some(e)) => he(t1, e)
      case VarDef(x, None) => false
      case LetDef(x, Some(e)) => he(t1, e)
      case LetDef(x, None) => false
      case ConstDef(x, Some(e)) => he(t1, e)
      case ConstDef(x, None) => false
      case While(e1, e2) => he(t1, e1) || he(t2, e2)
      case DoWhile(e1, e2) => he(t1, e1) || he(t2, e2)
      case With(e1, e2) => he(t1, e1) || he(t2, e2)
      case Residual(e) => he(t1, e)
      case _ => false
    }

    def coupling(t1: Node, t2: Node): Boolean = (t1, t2) match {
      case (Unary(op1, a1), Unary(op2, a2)) => op1 == op2 && he(a1, a2)
      case (Binary(op1, f1, a1), Binary(op2, f2, a2)) => op1 == op2 && he(f1, f2) && he(a1, a2)
      case (Assign(op1, f1, a1), Assign(op2, f2, a2)) => op1 == op2 && he(f1, f2) && he(a1, a2)
      case (IncDec(op1, e1), IncDec(op2, e2)) => op1 == op2 && he(e1, e2)
      case (Delete(e1), Delete(e2)) => he(e1, e2)
      case (New(e1), New(e2)) => he(e1, e2)
      case (Typeof(e1), Typeof(e2)) => he(e1, e2)
      case (Void(e1), Void(e2)) => he(e1, e2)
      case (Access(e1, x1), Access(e2, x2)) => x1 == x2 && he(e1, e2)
      case (Block(ss1), Block(ss2)) => ss1.length == ss2.length && (ss1 zip ss2).forall({ case (e1, e2) => he(e1, e2) })
      case (Break(_), Break(_)) => true
      case (Continue(_), Continue(_)) => true
      case (Call(e1, es1), Call(e2, es2)) => he(e1, e2) && (es1 zip es2).forall({ case (e1, e2) => he(e1, e2) })
      case (Case(f1, a1), Case(f2, a2)) => he(f1, f2) && he(a1, a2)
      case (Catch(b1, c1, d1), Catch(b2, c2, d2)) => he(b1, b2) && he(c1, c2) && he(d1, d2)
      case (Empty(), Empty()) => true
      case (Eval(e1), Eval(e2)) => he(e1, e2)
      case (For(a1, b1, c1, d1), For(a2, b2, c2, d2)) => he(a1, a2) && he(b1, b2) && he(c1, c2) && he(d1, d2)
      case (FunDef(n1, xs1, e1), FunDef(n2, xs2, e2)) => n1 == n2 && he(e1, e2)
      case (Lambda(xs1, e1), Lambda(xs2, e2)) => he(e1, e2)
      case (Ident(_), Ident(_)) => true
      case (Index(a1, i1), Index(a2, i2)) => he(a1, a2) && he(i1, i2)
      case (Label(x1, e1), Label(x2, e2)) => x1 == x2 && he(e1, e2)
      case (ArrayLit(ss1), ArrayLit(ss2)) => ss1.length == ss2.length && (ss1 zip ss2).forall({ case (e1, e2) => he(e1, e2) })
      case (ObjectLit(ss1), ObjectLit(ss2)) => ss1.length == ss2.length && (ss1 zip ss2).forall({ case (e1, e2) => he(e1, e2) })
      case (Property(a1, i1), Property(a2, i2)) => he(a1, a2) && he(i1, i2)
      case (Return(Some(e1)), Return(Some(e2))) => he(e1, e2)
      case (Yield(Some(e1)), Yield(Some(e2))) => he(e1, e2)
      case (Return(None), Return(None)) => true
      case (Yield(None), Yield(None)) => true
      case (Switch(e1, es1), Switch(e2, es2)) => he(e1, e2) && (es1 zip es2).forall({ case (e1, e2) => he(e1, e2) })
      case (Cond(a1, b1, c1), Cond(a2, b2, c2)) => he(a1, a2) && he(b1, b2) && he(c1, c2)
      case (Try(a1, es1, Some(c1)), Try(a2, es2, Some(c2))) => he(a1, a2) && (es1 zip es2).forall({ case (e1, e2) => he(e1, e2) }) && he(c1, c2)
      case (Try(a1, es1, None), Try(a2, es2, None)) => he(a1, a2) && (es1 zip es2).forall({ case (e1, e2) => he(e1, e2) })
      case (Throw(e1), Throw(e2)) => he(e1, e2)
      case (VarDef(_, Some(e1)), VarDef(_, Some(e2))) => he(e1, e2)
      case (VarDef(_, None), VarDef(_, None)) => true
      case (LetDef(_, Some(e1)), LetDef(_, Some(e2))) => he(e1, e2)
      case (LetDef(_, None), LetDef(_, None)) => true
      case (ConstDef(_, Some(e1)), ConstDef(_, Some(e2))) => he(e1, e2)
      case (ConstDef(_, None), ConstDef(_, None)) => true
      case (While(a1, i1), While(a2, i2)) => he(a1, a2) && he(i1, i2)
      case (DoWhile(a1, i1), DoWhile(a2, i2)) => he(a1, a2) && he(i1, i2)
      case (With(a1, i1), With(a2, i2)) => he(a1, a2) && he(i1, i2)

      // Treat numbers specially.
      // We compare numbers for equality when they're small.
      // Otherwise, we say just return true.
      // This ensures we eventually stop if the numbers grow without
      // bound and nothing else changes.
      case (Num(k1), Num(k2)) => k1 == k2 || (k1.abs > 25 && k2.abs > 25)
      case (Loc(k1), Loc(k2)) => k1 == k2

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
