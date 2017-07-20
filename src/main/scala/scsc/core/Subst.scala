package scsc.core

import scsc.util.FreshVar

////////////////////////////////////////////////////////////////////////////
// Substitutions
////////////////////////////////////////////////////////////////////////////
trait Subst[Exp] {
  type Name = String
  type Subst = Map[Name, Exp]

  val name: NameExp
  def applySubst(s: Subst)(t: Exp): Exp
  trait NameExp {
    def unapply(e: Exp): Option[Name]
    def apply(x: Name): Exp
  }

  val emptySubst: Subst = Map.empty

  def singletonSubst(v: Name, t: Exp) = Map(v -> t)

  // Merge operations on substitutions.
  implicit class SubstOps(s1: Subst) {
    // left-biased non-conflicting merge
    def @@(s2: Subst) = {
      // val s3 = for { (u, t) <- s2 } yield (u, applySubst(s1)(t))
      val s3 = for { (u, t) <- s2 -- s1.keys } yield (u, applySubst(s1)(t))
      val s4 = for { u <- s1.keys.toList intersect s2.keys.toList } yield s2(u) match {
                  case name(v) => (v, s1(u))
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
