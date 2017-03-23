package scsc.supercompile

import com.typesafe.scalalogging._

// Context reduction.
// The goal of context reduction is to reduce the list of predicates to
// a smaller, more managable list.
object MSG {
  import scsc.syntax.LambdaSyntax._
  import scsc.syntax.Trees._
  import scsc.syntax.FreeVars._

  val logger = Logger("MSG")

  type Subst = Map[Name, Exp]

  val emptySubst: Subst = Map.empty

  def singletonSubst(v: Name, t: Exp) = Map(v -> t)

  // Merge operations on substitutions.
  implicit class SubstOps(s1: Subst) {
    // left-biased non-conflicting merge
    def @@(s2: Subst) = {
      // val s3 = for { (u, t) <- s2 } yield (u, t.subst(s1))
      val s3 = for { (u, t) <- s2 -- s1.keys } yield (u, t.subst(s1))
      val s4 = for { u <- s1.keys.toList intersect s2.keys.toList }
        yield s2(u) match {
          case t @ Var(v) => (v, s1(u))
          case t => (u, t.subst(s1))
        }
      val s5 = s3 ++ s4 ++ s1
      s5
    }

    // merge where conflicts are an error
    def merge(s2: Subst): Option[Subst] = {
      val agree = (s1.keys.toList intersect s2.keys.toList).forall(v => s1(v) == s2(v))
      if (agree)
        Some(s1 ++ s2)
      else
        None
    }
  }

  implicit class ExpSubst(t: Exp) {
    def subst(s: Subst): Exp = t match {
      case Var(v) => s.get(v) match {
        case Some(u) => u
        case None => t
      }
      case Num(_) => t
      case Ctor(k, es) => Ctor(k, es.map(_.subst(s)))
      case Lam(x, e) => Lam(x, e.subst(s - x))
      case Let(x, e1, e2) => Let(x, e1.subst(s), e2.subst(s - x))
      case Letrec(x, e1, e2) => Letrec(x, e1.subst(s - x), e2.subst(s - x))
      case App(e1, e2) => App(e1.subst(s), e2.subst(s))
      case Bin(op, e1, e2) => Bin(op, e1.subst(s), e2.subst(s))
      case Not(e2) => Not(e2.subst(s))
      case Neg(e2) => Neg(e2.subst(s))
      case Case(e, alts) => Case(e.subst(s), alts.map { case Alt(p, e) => Alt(p, e.subst(s -- vars(p))) })
      case Residual(e) => Residual(e.subst(s))
    }
  }

  // Generalizes two terms, returning a new variable name,
  // a new lambda that should be bound to that variable, whose body is
  // the generalization, and then two applications of the new function,
  // equivalent to t1 and t2.
  def msgTerms(t1: Exp, t2: Exp): Option[(Name, Exp, Exp, Exp)] = {
    generalize(t1, t2) map {
      case (vars, s1, s2, t) =>
        // At this point, t is a generalization of t1 and t2,
        // but not necessarily the most specific generalization.
        // We have to identify variables in the two substitutions
        // that map to the same term.

        // s is a substitution built as follows.
        // if in s1, a and b both map to the same term
        // and in s2, a and b both map to the same term,
        // then replace b with a
        val s = for {
          (a, u) <- s1.toList
          (b, v) <- s1.toList
          if a < b        // always replace with the least variable
          if u == v                 // a and b map to the same type in s1
          if s2.get(a) == s2.get(b) // a and b map to the same type in s2, or s2 does not contain either a or b
        } yield (b, Var(a))
        logger.debug("  s1 = " + s1)
        logger.debug("  s2 = " + s2)
        logger.debug("   s = " + s.toMap)
        val f = FreshVar()
        val vars1 = vars diff s.map(_._1)
        val lam = vars1.foldRight(t.subst(s.toMap): Exp) {
          case (x, e) => Lam(x, e)
        }
        val app1 = vars1.foldLeft(Var(f): Exp) {
          case (e, x) => App(e, s1(x))
        }
        val app2 = vars1.foldLeft(Var(f): Exp) {
          case (e, x) => App(e, s2(x))
        }

        val vars2 = fv(lam).toList

        val vapp1 = vars2.foldLeft(app1: Exp) {
          case (e, x) => App(e, Var(x))
        }
        val vapp2 = vars2.foldLeft(app2: Exp) {
          case (e, x) => App(e, Var(x))
        }
        val vlam = vars2.foldRight(lam: Exp) {
          case (x, lam) => Lam(x, lam)
        }

        // Bind f to a new lambda that generalizes t1 and t2.
        // app1 and app2 are calls to f that should be equivalent to t1 and t2.
        (f, vlam, vapp1, vapp2)
    }
  }

  // Generalize two terms, if possible.
  // Returns vars, s1, s2, and t such that t1 == s1(t) and t2 == s2(t)
  //   and vars are the newly introduced variables in the generalized types.
  // Fails if t1 and t2 have different types (unimplemented).
  private def generalize(t1: Exp, t2: Exp): Option[(List[Name], Subst, Subst, Exp)] = (t1, t2) match {
    case (Var(a), Var(b)) if a == b => Some((Nil, emptySubst, emptySubst, Var(a)))
    case (Num(a), Num(b)) if a == b => Some((Nil, emptySubst, emptySubst, Num(a)))
    // FIXME
    case (Lam(ax, a), Lam(bx, b)) if ax == bx =>
      for {
        (vars, sa, sb, c) <- generalize(a, b)
      } yield (vars, sa, sb, Lam(ax, c))
    case (Let(ax, a1, a2), Let(bx, b1, b2)) if ax == bx && a1 == b1 =>
      for {
        (vars, sa, sb, c2) <- generalize(a2, b2)
      } yield (vars, sa, sb, Let(ax, a1, c2))
    case (Letrec(ax, a1, a2), Letrec(bx, b1, b2)) if ax == bx && a1 == b1 =>
      for {
        (vars, sa, sb, c2) <- generalize(a2, b2)
        // TODO
        // if ! fv(sa) contains ax
        // if ! fv(sb) contains pa
      } yield (vars, sa, sb, Letrec(ax, a1, c2))
    case (Ctor(ka, Nil), Ctor(kb, Nil)) if ka == kb =>
      Some((Nil, emptySubst, emptySubst, Ctor(ka, Nil)))
    case (Ctor(ka, a::as), Ctor(kb, b::bs)) if ka == kb =>
      for {
        (varsHd, sa, sb, hd) <- generalize(a, b)
        (varsTl, sas, sbs, Ctor(_, tl)) <- generalize(Ctor(ka, as), Ctor(kb, bs))
      } yield (varsHd ++ varsTl, sa @@ sas, sb @@ sbs, Ctor(ka, hd::tl))
    case (App(l1, r1), App(l2, r2)) =>
      for {
        (vars1, sl1, sl2, tl) <- generalize(l1, l2)
        (vars2, sr1, sr2, tr) <- generalize(r1, r2)
      } yield (vars1 ++ vars2, sl1 @@ sr1, sl2 @@ sr2, App(tl, tr))
    case (Bin(op1, l1, r1), Bin(op2, l2, r2)) if op1 == op2 =>
      for {
        (vars1, sl1, sl2, tl) <- generalize(l1, l2)
        (vars2, sr1, sr2, tr) <- generalize(r1, r2)
      } yield (vars1 ++ vars2, sl1 @@ sr1, sl2 @@ sr2, Bin(op1, tl, tr))
    case (Not(r1), Not(r2)) =>
      for {
        (vars2, sr1, sr2, tr) <- generalize(r1, r2)
      } yield (vars2, sr1, sr2, Not(tr))
    case (Neg(r1), Neg(r2)) =>
      for {
        (vars2, sr1, sr2, tr) <- generalize(r1, r2)
      } yield (vars2, sr1, sr2, Neg(tr))
    case (Case(r1, alts1), Case(r2, alts2)) if alts1 == alts2 =>
      for {
        (vars2, sr1, sr2, tr) <- generalize(r1, r2)
      } yield (vars2, sr1, sr2, Case(tr, alts1))
    case (t1, t2) if t1 == t2 =>
      Some((Nil, emptySubst, emptySubst, t1))
    case (t1, t2) =>
      // head of the terms not equal. Introduce a new variable.
      val a = FreshVar()
      Some((a::Nil, singletonSubst(a, t1), singletonSubst(a, t2), Var(a)))
  }

}
