package scsc.core

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._

object Residualization {
  def reify(e: Exp): Exp = {
    import scsc.js.TreeWalk._

    object Reify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Path(_, path) => super.rewrite(path)
        case e => super.rewrite(e)
      }
    }

    Reify.rewrite(e)
  }

  def unreify(e: Exp): Exp = {
    import scsc.js.TreeWalk._

    object Unreify extends Rewriter {
      override def rewrite(e: Exp): Exp = e match {
        case Residual(x) => Local(x)
        case e => super.rewrite(e)
      }
    }

    Unreify.rewrite(e)
  }
}
