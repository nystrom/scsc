package scsc.jssc

import scsc.js.Trees._
import Continuations._
import Subst._

class Unifier(protected var currSubst: Subst, protected var failed: Boolean) {
  import Unifier._

  def this() = this(emptySubst, false)

  def unify(t1: Exp, t2: Exp): Option[Subst] = {
    val s = currSubst
    mgu(t1.subst(s), t2.subst(s)) match {
      case Some(s) =>
        currSubst = s @@ currSubst
        Some(currSubst)
      case None =>
        failed = true
        None
    }
  }

  def unify(t1: Cont, t2: Cont): Option[Subst] = {
    val s = currSubst
    mguk(t1.subst(s), t2.subst(s)) match {
      case Some(s) =>
        currSubst = s @@ currSubst
        Some(currSubst)
      case None =>
        failed = true
        None
    }
  }

  def getSubst = if (!failed) Some(currSubst) else None
}

object Unifier {
  def mgu(ts1: List[Exp], ts2: List[Exp]): Option[Subst] = {
    (ts1, ts2) match {
      case (Nil, Nil) => Some(emptySubst)
      case (t1 :: ts1, t2 :: ts2) => {
        for {
          s1 <- mgu(t1, t2)
          s2 <- mgu(ts1, ts2)
        } yield (s1 @@ s2)
      }
      case _ => None
    }
  }

  def mgu(e1: Exp, e2: Exp): Option[Subst] = {
    import scsc.js.TreeWalk._
    import scala.collection.mutable.ListBuffer

    class Preorder() extends Rewriter {
      val es: ListBuffer[Exp] = ListBuffer()

      override def rewrite(e: Exp) = {
        super.rewrite(e)
        es += e
        e
      }
    }

    // Rather than traversing both trees in sync, just flatten them
    // into lists and check if the nodes in the tree are the same type,
    // unifying residual variables.

    val p1 = new Preorder()
    val p2 = new Preorder()
    p1.rewrite(e1)
    p2.rewrite(e2)

    val es1 = p1.es.toList
    val es2 = p2.es.toList

    if (es1.length == es2.length) {
      (es1 zip es2).foldLeft (Some(emptySubst): Option[Subst]) {
        case (None, _) => None
        case (Some(s), (Residual(x1), Residual(x2))) if x1 == x2 => Some(s)
        case (Some(s), (Residual(x1), Residual(x2))) if x1 < x2 => Some(s @@ singletonSubst(x1, Residual(x2)))
        case (Some(s), (Residual(x1), Residual(x2))) if x1 > x2 => Some(s @@ singletonSubst(x2, Residual(x1)))
        case (Some(s), (Residual(x1), e2)) => Some(s @@ singletonSubst(x1, e2))
        // Unification is asymmetric.
        // case (Some(s), (e1, Residual(x2))) => Some(s @@ singletonSubst(x2, e1))
        case (Some(s), (Binary(op1, _, _), Binary(op2, _, _))) if op1 == op2 => Some(s)
        case (Some(s), (Unary(op1, _), Unary(op2, _))) if op1 == op2 => Some(s)
        case (Some(s), (Assign(op1, _, _), Assign(op2, _, _))) if op1 == op2 => Some(s)
        case (Some(s), (IncDec(op1, _), IncDec(op2, _))) if op1 == op2 => Some(s)
        case (Some(s), (Break(label1), Break(label2))) if label1 == label2 => Some(s)
        case (Some(s), (Continue(label1), Continue(label2))) if label1 == label2 => Some(s)
        case (Some(s), (While(label1, _, _), While(label2, _, _))) if label1 == label2 => Some(s)
        case (Some(s), (DoWhile(label1, _, _), DoWhile(label2, _, _))) if label1 == label2 => Some(s)
        case (Some(s), (For(label1, _, _, _, _), For(label2, _, _, _, _))) if label1 == label2 => Some(s)
        case (Some(s), (ForIn(label1, _, _, _), ForIn(label2, _, _, _))) if label1 == label2 => Some(s)
        case (Some(s), (e1, e2)) if e1.getClass == e2.getClass => Some(s)
        case (Some(s), _) => None
      }
    }
    else {
      None
    }
  }

  def mguk(ts1: Cont, ts2: Cont): Option[Subst] = {
    (ts1, ts2) match {
      case (Nil, Nil) => Some(emptySubst)
      case (t1 :: ts1, t2 :: ts2) => {
        for {
          s1 <- mgu(t1, t2)
          s2 <- mguk(ts1, ts2)
        } yield (s1 @@ s2)
      }
      case _ => None
    }
  }

  implicit class OSOps(o1: Option[Subst]) {
    def @@(o2: Option[Subst]) = for {
      s1 <- o1
      s2 <- o2
    } yield s1 @@ s2
  }

  def mgu(k1: ContFrame, k2: ContFrame): Option[Subst] = (k1, k2) match {
    case (EvalMoreArgs(fun1, thisValue1, todo1, done1, ρ1), EvalMoreArgs(fun2, thisValue2, todo2, done2, ρ2)) if ρ1 == ρ2 => mgu(fun1, fun2) @@ mgu(thisValue1, thisValue2) @@ mgu(todo1, todo2) @@ mgu(done1, done2)
    case (EvalMoreArgsForResidual(fun1, todo1, done1, ρ1), EvalMoreArgsForResidual(fun2, todo2, done2, ρ2)) if ρ1 == ρ2 => mgu(fun1, fun2) @@ mgu(todo1, todo2) @@ mgu(done1, done2)
    case (EvalArgs(thisValue1, todo1, ρ1), EvalArgs(thisValue2, todo2, ρ2)) if ρ1 == ρ2 => mgu(thisValue1, thisValue2) @@ mgu(todo1, todo2)
    case (EvalMoreArgsForNew(fun1, todo1, done1, ρ1), EvalMoreArgsForNew(fun2, todo2, done2, ρ2)) if ρ1 == ρ2 => mgu(fun1, fun2) @@ mgu(todo1, todo2) @@ mgu(done1, done2)
    case (EvalMoreArgsForNewResidual(fun1, todo1, done1, ρ1), EvalMoreArgsForNewResidual(fun2, todo2, done2, ρ2)) if ρ1 == ρ2 => mgu(fun1, fun2) @@ mgu(todo1, todo2) @@ mgu(done1, done2)
    case (EvalArgsForNew(todo1, ρ1), EvalArgsForNew(todo2, ρ2)) if ρ1 == ρ2 => mgu(todo1, todo2)
    case (InitProto(fun1, args1, ρ1), InitProto(fun2, args2, ρ2)) if ρ1 == ρ2 => mgu(fun1, fun2) @@ mgu(args1, args2)
    case (EvalMethodProperty(methodProp1, args1, ρ1), EvalMethodProperty(methodProp2, args2, ρ2)) if ρ1 == ρ2 => mgu(methodProp1, methodProp2) @@ mgu(args1, args2)

    case (CallFrame(ρ1), CallFrame(ρ2)) if ρ1 == ρ2 => Some(emptySubst)
    case (CatchFrame(cs1, ρ1), CatchFrame(cs2, ρ2)) if ρ1 == ρ2 => mgu(cs1, cs2)
    case (FinallyFrame(fin1, ρ1), FinallyFrame(fin2, ρ2)) if ρ1 == ρ2 => mgu(fin1, fin2)

    // Unary operators
    case (DoUnaryOp(op1, ρ1), DoUnaryOp(op2, ρ2)) if op1 == op2 && ρ1 == ρ2 => Some(emptySubst)

    // Binary operators.
    case (EvalBinaryOpRight(op1, e1, ρ1), EvalBinaryOpRight(op2, e2, ρ2)) if op1 == op2 && ρ1 == ρ2 => mgu(e1, e2)
    case (DoBinaryOp(op1, v1, ρ1), DoBinaryOp(op2, v2, ρ2)) if op1 == op2 && ρ1 == ρ2 => mgu(v1, v2)

    case (SeqCont(e1, ρ1), SeqCont(e2, ρ2)) if ρ1 == ρ2 => mgu(e1, e2)
    case (FocusCont(v1), FocusCont(v2)) => mgu(v1, v2)
    case (BranchCont(ifTrue1: Cont, ifFalse1: Cont, ρ1), BranchCont(ifTrue2: Cont, ifFalse2: Cont, ρ2)) if ρ1 == ρ2 => mguk(ifTrue1, ifTrue2) @@ mguk(ifFalse1, ifFalse2)
    case (BreakFrame(label1), BreakFrame(label2)) if label1 == label2 => Some(emptySubst)
    case (ContinueFrame(label1), ContinueFrame(label2)) if label1 == label2 => Some(emptySubst)

    case (DoReturn(), DoReturn()) => Some(emptySubst)
    case (DoThrow(), DoThrow()) => Some(emptySubst)

    // Assignment.
    case (EvalAssignRhs(op1, rhs1, ρ1), EvalAssignRhs(op2, rhs2, ρ2)) if op1 == op2 && ρ1 == ρ2 => mgu(rhs1, rhs2)
    case (DoAssign(op1, lhs1, ρ1), DoAssign(op2, lhs2, ρ2)) if op1 == op2 && ρ1 == ρ2 => mgu(lhs1, lhs2)

    // ++, --, etc.
    case (DoIncDec(op1, ρ1), DoIncDec(op2, ρ2)) if op1 == op2 && ρ1 == ρ2 => Some(emptySubst)

    // typeof
    case (DoTypeof(ρ1), DoTypeof(ρ2)) if ρ1 == ρ2 => Some(emptySubst)

    // delete a[i]
    case (EvalPropertyNameForDel(i1, ρ1), EvalPropertyNameForDel(i2, ρ2)) if ρ1 == ρ2 => mgu(i1, i2)
    case (DoDeleteProperty(a1, ρ1), DoDeleteProperty(a2, ρ2)) if ρ1 == ρ2 => mgu(a1, a2)

    // a[i]
    case (EvalPropertyNameForGet(i1, ρ1), EvalPropertyNameForGet(i2, ρ2)) if ρ1 == ρ2 => mgu(i1, i2)
    case (GetProperty(a1, ρ1), GetProperty(a2, ρ2)) if ρ1 == ρ2 => mgu(a1, a2)

    // a[i] = v
    case (EvalPropertyNameForSet(i1, ρ1), EvalPropertyNameForSet(i2, ρ2)) if ρ1 == ρ2 => mgu(i1, i2)
    case (GetPropertyAddressOrCreate(a1, ρ1), GetPropertyAddressOrCreate(a2, ρ2)) if ρ1 == ρ2 => mgu(a1, a2)

    case _ => None
  }
}
