package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

// We start with a CEK machine for the lambda calculus.
object JSHE {
  import Machine._
  import scsc.core.Residualization._
  import Continuations._
  import States._

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

  def size(e: Exp): Int = {
    import scsc.js.TreeWalk._

    object Sizer extends Rewriter {
      var size = 0

      override def rewrite(e: Exp) = e match {
        case Num(n) if n.abs < 100 =>
          size += n.abs.toInt + 1
          e
        case Num(n) =>
          size += 101
          e
        case e =>
          size += 1
          super.rewrite(e)
      }
    }

    Sizer.rewrite(e)
    Sizer.size
  }

  implicit class StoreHE(σ1: Store) {
    def <<|(σ2: Store): Boolean = {
      val locs1 = σ1.keySet
      val locs2 = σ2.keySet
      (locs1 subsetOf locs2) && locs1.exists {
        loc =>
          ExpHE.he(σ1(loc), σ2(loc))
      }
    }
  }

  // Homeomorphic embedding code
  implicit class ExpHE(e1: Exp) {
    def <<|(e2: Exp): Boolean = {
      size(e1) <= size(e2) && ExpHE.he(e1, e2)
    }
  }

  object ExpHE {
    def he(v1: Closure, v2: Closure): Boolean = (v1, v2) match {
      case (ValClosure(v1), ValClosure(v2)) => he(v1, v2)
      case _ => false
    }

    def he(e1: Exp, e2: Exp): Boolean = diving(e1, e2) || coupling(e1, e2)

    def he(e1: Option[Exp], e2: Option[Exp]): Boolean = (e1, e2) match {
      case (Some(e1), Some(e2)) => he(e1, e2)
      case (Some(e1), None) => false
      case (None, Some(e2)) => false
      case (None, None) => true
    }

    def he(e1: Exp, e2: Option[Exp]): Boolean = e2.exists(he(e1, _))
    def he(e1: Exp, e2: List[Exp]): Boolean = e2.exists(he(e1, _))

    def diving(t1: Exp, t2: Exp): Boolean = {
      import scsc.js.TreeWalk._

      object Diver extends Rewriter {
        var yes = false

        override def rewrite(e: Exp): Exp = e match {
          case Break(_) | Continue(_) => e
          case Empty() => e
          case Local(_) => e
          case Return(None) | Yield(None) => e
          case Prim(_) => e
          // case Loc(_) => e
          case Path(_, _) => e
          case e if yes => e
          case e if e eq t2 => e // skip t2 to avoid infinite loop
          case e =>
            if (he(t1, e)) {
              yes = true
              // abort the traversal
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

    def coupling(t1: Exp, t2: Exp): Boolean = (t1 eq t2) || (t1 == t2) || coupling2(t1, t2)

    def coupling2(t1: Exp, t2: Exp): Boolean = (t1, t2) match {
      case (Scope(a1), Scope(a2)) => he(a1, a2)
      case (Prim(a1), Prim(a2)) => a1 == a2
      case (Unary(op1, a1), Unary(op2, a2)) => op1 == op2 && he(a1, a2)
      case (Binary(op1, f1, a1), Binary(op2, f2, a2)) => op1 == op2 && he(f1, f2) && he(a1, a2)
      case (Assign(op1, f1, a1), Assign(op2, f2, a2)) => op1 == op2 && he(f1, f2) && he(a1, a2)
      case (IncDec(op1, e1), IncDec(op2, e2)) => op1 == op2 && he(e1, e2)
      case (Delete(e1), Delete(e2)) => he(e1, e2)
      case (New(e1), New(e2)) => he(e1, e2)
      case (Typeof(e1), Typeof(e2)) => he(e1, e2)
      case (Void(e1), Void(e2)) => he(e1, e2)
      case (Break(_), Break(_)) => true
      case (Continue(_), Continue(_)) => true
      case (Call(e1, es1), Call(e2, es2)) => he(e1, e2) && (es1 zip es2).forall({ case (e1, e2) => he(e1, e2) })
      case (Case(f1, a1), Case(f2, a2)) => he(f1, f2) && he(a1, a2)
      case (Catch(b1, c1, d1), Catch(b2, c2, d2)) => b1 == b2 && he(c1, c2) && he(d1, d2)
      case (Empty(), Empty()) => true
      case (For(label1, a1, b1, c1, d1), For(label2, a2, b2, c2, d2)) => label1 == label2 && he(a1, a2) && he(b1, b2) && he(c1, c2) && he(d1, d2)
      case (ForEach(label1, a1, b1, c1, d1), ForEach(label2, a2, b2, c2, d2)) => label1 == label2 && he(a1, a2) && he(b1, b2) && he(c1, c2) && he(d1, d2)
      case (ForIn(label1, a1, b1, c1), ForIn(label2, a2, b2, c2)) => label1 == label2 && he(a1, a2) && he(b1, b2) && he(c1, c2)
      case (Lambda(xs1, e1), Lambda(xs2, e2)) => he(e1, e2)
      case (Local(_), Local(_)) => true
      case (Index(a1, i1), Index(a2, i2)) => he(a1, a2) && he(i1, i2)
      case (ArrayLit(ss1), ArrayLit(ss2)) => ss1.length == ss2.length && (ss1 zip ss2).forall({ case (e1, e2) => he(e1, e2) })
      case (Seq(a1, i1), Seq(a2, i2)) => he(a1, a2) && he(i1, i2)
      case (ObjectLit(ss1), ObjectLit(ss2)) => ss1.length == ss2.length && (ss1 zip ss2).forall({ case (e1, e2) => he(e1, e2) })
      case (Property(a1, i1, g1, s1), Property(a2, i2, g2, s2)) => he(a1, a2) && he(i1, i2) && he(g1, g2) && he(s1, s2)
      case (Return(e1), Return(e2)) => he(e1, e2)
      case (Yield(e1), Yield(e2)) => he(e1, e2)
      case (Switch(e1, es1), Switch(e2, es2)) => he(e1, e2) && (es1 zip es2).forall({ case (e1, e2) => he(e1, e2) })
      case (Cond(a1, b1, c1), Cond(a2, b2, c2)) => he(a1, a2) && he(b1, b2) && he(c1, c2)
      case (IfElse(a1, b1, c1), IfElse(a2, b2, c2)) => he(a1, a2) && he(b1, b2) && he(c1, c2)
      case (TryCatch(a1, es1), TryCatch(a2, es2)) => he(a1, a2) && (es1 zip es2).forall({ case (e1, e2) => he(e1, e2) })
      case (TryFinally(a1, c1), TryFinally(a2, c2)) => he(a1, a2) && he(c1, c2)
      case (Throw(e1), Throw(e2)) => he(e1, e2)
      case (VarDef(_, e1), VarDef(_, e2)) => he(e1, e2)
      case (While(label1, a1, i1), While(label2, a2, i2)) => label1 == label2 && he(a1, a2) && he(i1, i2)
      case (DoWhile(label1, a1, i1), DoWhile(label2, a2, i2)) => label1 == label2 && he(a1, a2) && he(i1, i2)
      case (With(a1, i1), With(a2, i2)) => he(a1, a2) && he(i1, i2)

      // Treat numbers specially.
      // We compare numbers for equality when they're small.
      // Otherwise, we say just return true.
      // This ensures we eventually stop if the numbers grow without
      // bound and nothing else changes.
      case (Num(k1), Num(k2)) => k1 == k2 || (k1.abs > 25 && k2.abs > 25)

      // Ignore names for heap locations, residual variables
      // and also local variables (above)
      case (Path(k1, _), Path(k2, _)) => true
      case (Residual(_), Residual(_)) => true

      case _ => false
    }
  }

  implicit class StHE(s1: St) {
    def comparableConts(k1: Cont, k2: Cont) = (k1, k2) match {
      case (Nil, Nil) => true
      case (k1::_, k2::_) => k1.getClass == k2.getClass
      case _ => false
    }

    def comparableStates(s1: St, s2: St): Boolean = (s1, s2) match {
      case (s1 @ Ev(e1, ρ1, σ1, φ1, k1), s2 @ Ev(e2, ρ2, σ2, φ2, k2)) => e1 == e2 && φ1 == φ2 && comparableConts(k1, k2)
      case (s1 @ Unwinding(jump1, σ1, φ1, k1), s2 @ Unwinding(jump2, σ2, φ2, k2)) => jump1 == jump2 && φ1 == φ2 && comparableConts(k1, k2)
      case (s1 @ Co(v1, σ1, φ1, k1), s2 @ Co(v2, σ2, φ2, k2)) => v1 == v2 && φ1 == φ2 && comparableConts(k1, k2)
      case (s1 @ Rebuild(t1), s2 @ Rebuild(t2)) => comparableStates(t1, t2)
      case _ => false
    }

    def <<|(s2: St): Boolean = (s1, s2) match {
      // Only compare states if the focus expression is the same and the first continuation
      // is of the same type. That is, we're evaluatnig the same expression in
      // a similar context.
      // Otherwise, we might have too many false positives.
      //
      // FIXME: currently the whistle blows a bit too often.
      // For instance, with the logarithmic version of pow.
      // Need to incorporate the environment too, perhaps.
      case (s1, s2) if comparableStates(s1, s2) =>
        def toFinalState(s: St) = {
          // Just drive getting stuck at each Ev
          JSDrive.drive(Nil, Nil, true)(s) match {
            case (s, memo) => s
          }
        }

        (toFinalState(s1), toFinalState(s2)) match {
          case (u1 @ Halt(e1, σ1, φ1), u2 @ Halt(e2, σ2, φ2)) =>
            val t1 = u1.residual
            val t2 = u2.residual

            val n1 = size(t1)
            val n2 = size(t2)

            println("HE: comparing " + s1)
            println("           vs " + s2)
            println("HE:   reduced " + u1)
            println("           vs " + u2)
            println("HE:     terms " + t1.show)
            println("           vs " + t2.show)
            println("HE:     sizes " + n1)
            println("           vs " + n2)

            n1 <= n2 && t1 <<| t2
          case (s1 @ Err(_, _), s2 @ Err(_, _)) =>
            // if both fail, blow the whistle!
            true
          case (u1, u2) =>
            println("final states $u1 vs $u2")
            false
        }
      case _ => false
    }
  }
}