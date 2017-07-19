package scsc.core

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

trait HEShapeless[Term] {
  import shapeless._
  import shapeless.ops.hlist._

  implicit class HEOps(a: Term) {
    def ◁(b: Term)(implicit d: Diving[Term, Term], c: Coupling[Term]) = d.heByDiving(a)(b) || c.heByCoupling(a, b)
  }

  // Dive on A looking for an embedding of Q
  trait Diving[A, Q] {
    def heByDiving(b: Q)(a: A): Boolean
  }

  trait LowestPriorityDiving {
    implicit def genericDiving[A, Q](implicit c: Coupling[A]): Diving[A, Q] = new Diving[A, Q] {
      def heByDiving(b: Q)(a: A) = false
    }
  }

  trait LowerPriorityDiving extends LowestPriorityDiving {
    implicit def hlistishDiving[A, L <: HList, Q](
      implicit gen: Generic.Aux[A, L],
      d: Diving[L, Q],
      c: Coupling[L]
    ): Diving[A, Q] = new Diving[A, Q] {
      def heByDiving(b: Q)(a: A) = d.heByDiving(b)(gen to a)
    }
  }

  trait LowPriorityDiving extends LowerPriorityDiving {
    implicit def listDiving[A, Q](implicit d: Diving[A, Q], c: Coupling[A]) = {
      new Diving[List[A], Q] {
        def heByDiving(b: Q)(a: List[A]) = a.exists(d.heByDiving(b) _)
      }
    }

    implicit def optionDiving[A, Q](implicit d: Diving[A, Q], c: Coupling[A]) = {
      new Diving[Option[A], Q] {
        def heByDiving(b: Q)(a: Option[A]) = a.exists(d.heByDiving(b) _)
      }
    }

    implicit def hnilDiving[Q]: Diving[HNil, Q] = new Diving[HNil, Q] {
      def heByDiving(b: Q)(a: HNil) = false
    }

    implicit def hlistDiving[H, T <: HList, Q](implicit hd: Diving[H, Q], td: Diving[T, Q], hc: Coupling[H], tc: Coupling[T]) = {
      new Diving[H :: T, Q] {
        def heByDiving(b: Q)(a: H :: T) = hd.heByDiving(b)(a.head) || td.heByDiving(b)(a.tail)
      }
    }
  }

  object Diving extends LowPriorityDiving {
    implicit def elemDiving[A](implicit c: Coupling[A]): Diving[A, A] = new Diving[A, A] {
      def heByDiving(b: A)(a: A) = c.heByCoupling(a, b)
    }
  }

  // Dive on A looking for an embedding of Q
  trait Coupling[A] {
    def heByCoupling(a: A, b: A): Boolean
  }

  trait LowestPriorityCoupling {
    implicit def genericCoupling[A]: Coupling[A] = new Coupling[A] {
      def heByCoupling(a: A, b: A) = a == b
    }
  }

  trait LowerPriorityCoupling extends LowestPriorityCoupling {
    implicit def hlistishCoupling[A, L <: HList](
      implicit gen: Generic.Aux[A, L], s: Coupling[L]
    ): Coupling[A] = new Coupling[A] {
      def heByCoupling(a: A, b: A) = s.heByCoupling(gen to a, gen to b)
    }
  }

  trait LowPriorityCoupling extends LowerPriorityCoupling {
    implicit def listCoupling[A](implicit s: Coupling[A]) = {
      new Coupling[List[A]] {
        def heByCoupling(a: List[A], b: List[A]) = {
          a.length == b.length && (a zip b).forall { case (a, b) => s.heByCoupling(a, b) }
        }
      }
    }

    implicit def optionCoupling[A](implicit s: Coupling[A]) = {
      new Coupling[Option[A]] {
        def heByCoupling(a: Option[A], b: Option[A]) = (a, b) match {
          case (None, None) => true
          case (Some(a), Some(b)) => s.heByCoupling(a, b)
          case _ => false
        }
      }
    }

    implicit def hnilCoupling: Coupling[HNil] = new Coupling[HNil] {
      def heByCoupling(a: HNil, b: HNil) = true
    }

    implicit def hlistCoupling[H, T <: HList](implicit hs: Coupling[H], ts: Coupling[T]) = {
      new Coupling[H :: T] {
        def heByCoupling(a: H :: T, b: H :: T) = hs.heByCoupling(a.head, b.head) && ts.heByCoupling(a.tail, b.tail)
      }
    }
  }

  object Coupling extends LowPriorityCoupling {
    implicit def intCouping: Coupling[Int] = new Coupling[Int] {
      def heByCoupling(a: Int, b: Int) = {
        // Compare small numbers, but just lump all big numbers together.
        if (a.abs <= 10 || b.abs <= 10)
          a == b
        else
          a.abs <= 10 && b.abs <= 10
      }
    }
  }

  import Diving._
  import Coupling._
}
