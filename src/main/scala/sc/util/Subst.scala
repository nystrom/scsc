package sc.util

import shapeless._

////////////////////////////////////////////////////////////////////////////
// Substitutions
////////////////////////////////////////////////////////////////////////////
trait Subst[Name, Term] {
  // Convert between expressions and names.
  val AsName: AsName
  trait AsName {
    def unapply(e: Term): Option[Name]
    def apply(x: Name): Term
  }

  type Subst = Map[Name, Term]

  // Apply a substitution.
  // The default implementation does a naive substitution, ignoring bindings.
  def applySubst(s: Subst)(t: Term)(implicit typeable: Typeable[Term]): Term = {
    import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
    import org.bitbucket.inkytonik.kiama.rewriting.Strategy
    import org.bitbucket.inkytonik.kiama.util.Comparison.same

    val subst = rule[Term] {
      case e @ AsName(x) =>
        s.get(x) match {
          case Some(e1) => e1
          case None => e
        }
      case e => e
    }

    val IsTerm = TypeCase[Term]

    // If subst fails, just return the original expression
    everywhere(subst)(t) match {
      case Some(IsTerm(t)) => t
      case _ => t
    }
  }

  val emptySubst: Subst = Map.empty

  def singletonSubst(v: Name, t: Term) = Map(v -> t)

  // Merge operations on substitutions.
  implicit class SubstOps(s1: Subst) {
    // left-biased non-conflicting merge
    def @@(s2: Subst)(implicit typeable: Typeable[Term]) = {
      // val s3 = for { (u, t) <- s2 } yield (u, applySubst(s1)(t))
      val s3 = for { (u, t) <- s2 -- s1.keys } yield (u, applySubst(s1)(t))
      val s4 = for { u <- s1.keys.toList intersect s2.keys.toList } yield s2(u) match {
                  case AsName(v) => (v, s1(u))
                  case t => (u, applySubst(s1)(t))
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
}
