package scsc.core

import shapeless._

object SameHead {
  // Extractor that matches two expressions with the same head.
  // For example, (Add(1, 2), Add(3, 4)) matches, but (Add(1, 2), Mul(3, 4)) does not.
  // Default implementation just checks if they have the same product type.

  def unapply[Term](p: (Term, Term))(implicit typeable: Typeable[Term]): Option[(Term, Term)] = {
    val term = TypeCase[Term]
    p match {
      case (term(x), term(y)) if x.getClass == y.getClass => Some((x, y))
      case _ => None
    }
  }
}

/*
object ZipperTraverse {
  // Traverses two trees, mapping each pair of terms encountered to a new term.
  def zipWith[T](whenDifferent: (Option[Any], Option[Any]) => Any, sameHead: (Any, Any) => Option[Any])(a: T, b: T): T = {
    val missingLeft = b => whenDifferent(None, Some(b))
    val missingRight = a => whenDifferent(Some(a), None)
    val differentHead = (a, b) => whenDifferent(Some(a), Some(b))

    (a, b) match {
      case (a: Product, b: Product) if a.getClass == b.getClass =>
        sameHead(a, b) match {
          case Some(c) => c
          case None =>
            val i = zipWith(whenDifferent, sameHead)(a.productIterator, b.productIterator)
            dup(a, i.toArray)
        }
      // case (a: Map[_, _], b: Map[_, _]) =>
      //   sameHead(a, b) match {
      //     case Some(c) => c
      //     case None =>
      //       val aks = a.keySet
      //       val bks = b.keySet
      //       val m = MapBuilder
      //       for ((k, va) <- a.asInstanceOf[Map[Any, Any]]) {
      //         b.asInstanceOf[Map[Any, Any]].get(k) {
      //           case Some(vb) =>
      //             val (k1, v1) = zipWith(whenDifferent, sameHead)((k, va), (k, vb))
      //             m += (k1 -> v1)
      //           case None =>
      //             m += missingRight((k, va))
      //         }
      //       }
      //   }
      case (a: Seq[_], b: Seq[_]) if a.length == b.length =>
        sameHead(a, b) match {
          case Some(c) => c
          case None =>
            (a.asInstanceOf[Seq[Any]] zip b.asInstanceOf[Seq[Any]]) map {
              case (ai, bi) => zipWith(whenDifferent, sameHead)(ai, bi)
            }
        }
      case (a, b) =>
        differentHead(a, b)
    }
  }
}

*/

// object ZipperTraverse {
//   import shapeless._
//   import shapeless.ops.hlist._
//
//   // Traverse a and b in sync, zipping
//   def zipWith[Term](f: (Term, Term) => Term)(a: Term, b: Term)(implicit termGen: Generic[Term]) = {
//     object applyF extends Poly1 {
//       implicit def caseTuple = at[(Term, Term)] { case (x, y) => f(x, y) }
//     }
//
//     def zipAndMix[L <: HList, Z <: HList](h1: L, h2: L)(implicit
//       zipper: Zip.Aux[L :: L :: HNil, Z],
//       mapper: Mapper[applyF.type, Z]
//     ) = (h1 zip h2) map applyF
//
//     // convert the terms to hlists
//     val ta = termGen.to(a)
//     val tb = termGen.to(b)
//
//     zipAndMix(ta, tb)
//   }
// }
