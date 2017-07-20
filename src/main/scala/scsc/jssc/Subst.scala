package scsc.jssc

import scsc.js.Trees._

object Subst extends scsc.core.Subst[Exp] {
  // implement the trait
  object name extends NameExp {
    def unapply(e: Exp): Option[Name] = e match {
      case Residual(x) => Some(x)
      case _ => None
    }
    def apply(x: Name) = Residual(x)
  }

  def applySubst(s: Subst)(t: Exp): Exp = t.subst(s)

  import scsc.js.TreeWalk._
  import scsc.jssc.Continuations.Cont
  import scsc.js.TreeWalk.Rewriter
  import scsc.jssc.ContWalk.ContRewriter

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
