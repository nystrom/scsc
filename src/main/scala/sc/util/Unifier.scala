package sc.util

import shapeless.{Typeable, TypeCase}

trait Unifier[Name, Term] extends Subst[Name, Term] {

  class Unifier(protected var currSubst: Subst, protected var failed: Boolean) {
    import Unifier._

    def this() = this(emptySubst, false)

    def unify(t1: Term, t2: Term)(implicit typeable: Typeable[Term], nameOrd: Ordering[Name]): Option[Subst] = {
      val s = currSubst
      mgu(applySubst(s)(t1), applySubst(s)(t2)) match {
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
    def mgu(ts1: List[Term], ts2: List[Term])(implicit typeable: Typeable[Term], nameOrd: Ordering[Name]): Option[Subst] = {
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

    def mgu(e1: Term, e2: Term)(implicit typeable: Typeable[Term], nameOrd: Ordering[Name]): Option[Subst] = {
      import scala.collection.mutable.ListBuffer
      import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
      import org.bitbucket.inkytonik.kiama.rewriting.Strategy
      import org.bitbucket.inkytonik.kiama.util.Comparison.same
      import nameOrd._
      import typeable._

      lazy val nodes = collect[List, Any] {
        case n => n
      }

      val es1 = nodes(e1)
      val es2 = nodes(e2)

      val IsTerm = TypeCase[Term]

      if (es1.length == es2.length) {
        (es1 zip es2).foldLeft (Some(emptySubst): Option[Subst]) {
          case (None, _) => None
          case (Some(s), (IsTerm(AsName(x1)), IsTerm(AsName(x2)))) if x1 == x2 => Some(s)
          case (Some(s), (IsTerm(AsName(x1)), IsTerm(AsName(x2)))) if x1 < x2 => Some(s @@ singletonSubst(x1, AsName(x2)))
          case (Some(s), (IsTerm(AsName(x1)), IsTerm(AsName(x2)))) if x1 > x2 => Some(s @@ singletonSubst(x2, AsName(x1)))
          case (Some(s), (IsTerm(AsName(x1)), IsTerm(e2))) => Some(s @@ singletonSubst(x1, e2))
          case (Some(s), (IsTerm(e1), IsTerm(e2))) if e1 == e2 => Some(s)
          case (Some(s), SameHead(e1, e2)) => Some(s)
          case (Some(s), _) => None
        }
      }
      else {
        None
      }
    }

    implicit class OSOps(o1: Option[Subst]) {
      def @@(o2: Option[Subst])(implicit typeable: Typeable[Term]) = for {
        s1 <- o1
        s2 <- o2
      } yield s1 @@ s2
    }
  }
}
