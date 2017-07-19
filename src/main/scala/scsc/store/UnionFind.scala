package scsc.store

trait UnionFind[A, L] {
  def newLabel(a: A): L
  def mergeLabel(l1: L, l2: L): Option[L]

  import scala.collection.mutable.HashMap

  private class Node[L](var label: L, var size: Int, var next: Node[L])

  private val map = new HashMap[A, Node[L]]()

  private def newNode(a: A, label: L): Node[L] = {
    val n = new Node[L](label, 1, null)
    map.put(a, n)
    n
  }

  def relabel(x: A, label: L) = {
    findNode(x).label = label
  }

  def merge(x: A, y: A): Option[L] = {
    val rx = findNode(x)
    val ry = findNode(y)

    if (rx == ry) {
      Some(rx.label)
    }
    else {
      mergeLabel(rx.label, ry.label) map {
        case l => {
          if (rx.size < ry.size) {
            rx.next = ry
            ry.label = l
            ry.size += rx.size
          }
          else {
            ry.next = rx
            rx.label = l
            rx.size += ry.size
          }
          l
        }
      }
    }
  }

  def find(a: A): L = {
    findNode(a).label
  }

  private def findNode(a: A): Node[L] = {
    map.get(a) match {
      case None => newNode(a, newLabel(a))
      case Some(n) => getRoot(n)
    }
  }

  private def getRoot(n: Node[L]): Node[L] = {
    if (n.next != null) {
      val r = getRoot(n.next)
      mergeLabel(r.label, n.label) match {
        case Some(l) => {
          r.label = l
          // path compression
          n.next = r
          r
        }
        case None => {
          throw new RuntimeException("cannot merge labels with own root")
        }
      }
    }
    else {
      n
    }
  }
}
