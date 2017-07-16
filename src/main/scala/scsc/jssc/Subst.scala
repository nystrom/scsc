package scsc.jssc

import scsc.js.Trees._
import scsc.util.FreshVar

////////////////////////////////////////////////////////////////////////////
// Substitutions
////////////////////////////////////////////////////////////////////////////
object Subst {
  type Subst = Map[Name, Exp]

  val emptySubst: Subst = Map.empty

  // +-> in THIH
  def singletonSubst(v: Name, t: Exp) = Map(v -> t)

  // Merge operations on substitutions.
  implicit class SubstOps(s1: Subst) {
    // left-biased non-conflicting merge
    def @@(s2: Subst) = {
      // val s3 = for { (u, t) <- s2 } yield (u, t.subst(s1))
      val s3 = for { (u, t) <- s2 -- s1.keys } yield (u, t.subst(s1))
      val s4 = for { u <- s1.keys.toList intersect s2.keys.toList }
        yield s2(u) match {
          case Residual(v) => (v, s1(u))
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

  import scsc.js.TreeWalk._
  import Continuations.Cont
  import scsc.js.TreeWalk.Rewriter
  import ContWalk.ContRewriter

  class ExpSubst(s: Subst) extends Rewriter {
    override def rewrite(e: Exp) = e match {
      case Residual(x) =>
        s.get(x) match {
          case Some(e) => e
          case None => Residual(x)
        }
      case Local(x) =>
        s.get(x) match {
          case Some(e) => e
          case None => Local(x)
        }
      case e =>
        super.rewrite(e)
    }
  }

  class ContSubst(s: Subst) extends ContRewriter {
    def treeRewriter = new ExpSubst(s)
  }

  implicit class SubstExp(e: Exp) {
    def subst(s: Subst) = {
      new ExpSubst(s).rewrite(e)
    }
  }

  implicit class SubstCont(k: Cont) {
    def subst(s: Subst) = {
      new ContSubst(s).rewrite(k)
    }
  }
}
