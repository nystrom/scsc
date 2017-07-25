package sc.util

import com.typesafe.scalalogging._
import shapeless.{Typeable, TypeCase}

trait MSG[Name, Term] extends Subst[Name, Term] {
  val logger = Logger("MSG")

  def freshVar(): Name

  // Generalizes two terms, returning a new variable name,
  // a new lambda that should be bound to that variable, whose body is
  // the generalization, and then two applications of the new function,
  // equivalent to t1 and t2.
  def msgTerms(t1: Term, t2: Term)(implicit typeable: Typeable[Term], nameOrd: Ordering[Name]): Option[(Subst, Term)] = {
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
        import nameOrd._

        val s = for {
          (a, u) <- s1.toList
          (b, v) <- s1.toList
          if a < b                  // always replace with the least variable
          if u == v                 // a and b map to the same type in s1
          if s2.get(a) == s2.get(b) // a and b map to the same type in s2, or s2 does not contain either a or b
        } yield (b, AsName(a))

        logger.debug("  s1 = " + s1)
        logger.debug("  s2 = " + s2)
        logger.debug("   s = " + s.toMap)

        (s.toMap, t)
    }
  }

  // Generalize two terms, if possible.
  // Returns vars, s1, s2, and t such that t1 == s1(t) and t2 == s2(t)
  //   and vars are the newly introduced variables in the generalized term.
  // Fails if t1 and t2 have different types (unimplemented).
  private def generalize(t1: Term, t2: Term)(implicit typeable: Typeable[Term]): Option[(List[Name], Subst, Subst, Term)] = (t1, t2) match {
    case (AsName(a), AsName(b)) if a == b => Some((Nil, emptySubst, emptySubst, AsName(a)))
    case SameHead(t1, t2) =>
      Some((Nil, emptySubst, emptySubst, t1))
    case (t1, t2) =>
      val a = freshVar()
      Some((a::Nil, singletonSubst(a, t1), singletonSubst(a, t2), AsName(a)))
  }

}
