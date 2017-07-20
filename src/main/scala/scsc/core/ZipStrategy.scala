package scsc.core

import scala.collection.mutable.ListBuffer
import scala.collection.generic.CanBuildFrom
import scala.collection.immutable.Seq
import scala.language.higherKinds

object ZipStrategy {
  import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
  import org.bitbucket.inkytonik.kiama.rewriting.Strategy
  import org.bitbucket.inkytonik.kiama.util.Comparison.same

  def zip(strat: Strategy): Strategy = strategy[Any] {
    case (px: Product, py: Product) =>
      zipProduct(strat, px, py)
    case (tx: Seq[_], ty: Seq[_]) =>
      zipSeq(strat, tx.asInstanceOf[Seq[Any]], ty.asInstanceOf[Seq[Any]])
    case (tx: Map[_, _], ty: Map[_, _]) =>
      if (tx.keySet == ty.keySet) {
        None
      }
      val keys = tx.asInstanceOf[Map[Any, Any]].keySet
      zipSeq(strat, keys map { k => tx.asInstanceOf[Map[Any, Any]](k) } toList,
                    keys map { k => ty.asInstanceOf[Map[Any, Any]](k) } toList) match {
        case Some((sx, sy)) =>
          Some((sx.asInstanceOf[Seq[(Any, Any)]].toMap, sy.asInstanceOf[Seq[(Any, Any)]].toMap))
        case _ =>
          None
      }
      // zipMap(strat, tx.asInstanceOf[Map[Any, Any]], ty.asInstanceOf[Map[Any, Any]])
    case (x, y) =>
      strat((x, y))
  }

  def zipProduct(s: Strategy, px: Product, py: Product) : Option[(Any, Any)] = {
    if (! px.canEqual(py)) {
      // different classes
      None
    }
    else {
      val xArity = px.productArity
      val yArity = py.productArity

      if (xArity != yArity) {
        None
      }
      else if (xArity == 0) {
        Some((px, py))
      }
      else {
        val bx = Array.newBuilder[AnyRef]
        val by = Array.newBuilder[AnyRef]
        val ix = px.productIterator
        val iy = py.productIterator

        val changed = (ix zip iy).foldLeft(false) {
          case (changed, (x, y)) =>
            s((x, y)) match {
              case Some((x1, y1)) =>
                bx += x1.asInstanceOf[AnyRef]
                by += y1.asInstanceOf[AnyRef]
                changed || ! same(x, x1) || ! same(y, y1)
              case _ =>
                return None
            }
        }
        if (changed)
          Some((dup(px, bx.result), dup(py, by.result)))
        else
          Some((px, py))
      }
    }
  }

  def zipSeq[U, CC[+U] <: Seq[U]](s: Strategy, px: CC[U], py: CC[U])(implicit cbf : CanBuildFrom[CC[Any], Any, CC[Any]]): Option[(CC[Any], CC[Any])] = {
    val xArity = px.size
    val yArity = py.size

    if (xArity != yArity) {
      None
    }
    else if (xArity == 0) {
      Some((px, py))
    }
    else {
      val bx = cbf(px)
      val by = cbf(py)

      val changed = (px zip py).foldLeft(false) {
        case (changed, (x, y)) =>
          s((x, y)) match {
            case Some((x1, y1)) =>
              bx += x1
              by += y1
              changed || ! same(x, x1) || ! same(y, y1)
            case _ =>
              return None
          }
      }
      if (changed)
        Some((bx.result, by.result))
      else
        Some((px, py))
    }
  }

/*
  def zipMap[U, +V](s: Strategy, px: Map[U, V], py: Map[U, V])(implicit cbf: CanBuildFrom[Map[U, Any], (Any, Any), Map[U, Any]]): Option[(Map[U, Any], Map[U, Any])] = {
    val xks = px.keySet
    val yks = py.keySet

    if (xks != yks) {
      return None
    }

    val bx = cbf(px)
    val by = cbf(py)

    val changed = xks.foldLeft(false) {
      case (changed, k) =>
        s((k, k)) match {
          case Some((kx, ky)) =>
            s((px(k), py(k))) match {
              case Some((vx, vy)) =>
                bx += (kx -> vx)
                by += (ky -> vy)
                changed || ! same(k, kx) || ! same(k, ky) || ! same(px(k), vx) || ! same(py(k), vy)
            }
          case _ =>
            return None
        }
    }
    if (changed)
      Some((bx.result, by.result))
    else
      Some((px, py))
  }
  */
}
