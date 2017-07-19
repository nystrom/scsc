package scsc.core

import scala.collection.mutable.ListBuffer
import scala.collection.generic.CanBuildFrom
import scala.collection.immutable.Seq
import scala.language.higherKinds

trait HE[Term] {
  import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
  import org.bitbucket.inkytonik.kiama.rewriting.Strategy
  import org.bitbucket.inkytonik.kiama.util.Comparison.same
  import ZipStrategy._

  implicit class HEOps(t1: Term) {
    def ◁(t2: Term) = same(t1, t2) || coupling(t1, t2)
    def ≈(t2: Term) = t1 == t2
  }

  protected def embedded[A](x: A, y: A): Boolean = {
    same(x, y) || diving(x, y) || coupling(x, y)
  }

  protected def coupling[A](x: A, y: A): Boolean = {
    var c = false

    val xroot = x
    val yroot = y

    lazy val coupling: Strategy = strategy[(Any, Any)] {
      case (x, y) if same(x, xroot) || same(y, yroot) =>
        // don't recurse on the original arguments
        Some((x, y))
      case (x, y) if c =>
        Some((x, y))
      case (x, y) =>
        c |= (same(x, y) || diving(x, y))
        Some((x, y))
    }

    zip(coupling)((xroot, yroot))
    c
  }

  protected def diving[A, B](x: A, y: B): Boolean = {
    val yroot = y
    var c = false
    lazy val diving: Strategy = strategy[Any] {
      case y if same(y, yroot) =>
        // don't recurse on the original arguments
        Some(y)
      case y =>
        c |= (same(x, y) || coupling(x, y))
        Some(y)
    }
    everywhere(diving)(yroot)
    c
  }
}
