package scsc.core

trait Whistles extends SCConfigs with SCGraphs {
  type NormalConfig <: AnyRef

  // Normalize the configuration for HE or memoization.
  def normalize(c: Config): NormalConfig

  def isInstance(c1: NormalConfig, c2: NormalConfig): Boolean = {
    object HE extends scsc.core.HE[NormalConfig]
    import HE._
    (c1 eq c2) || (c1 ≈ c2)
  }

  def isSmaller(child: NormalConfig, ancestor: NormalConfig): Boolean = {
    object HE extends scsc.core.HE[NormalConfig]
    import HE._
    (child eq ancestor) || (ancestor ◁ child)
  }

  // Return true if the configuration MIGHT diverge and should therefore
  // be tested using isSmaller.
  def mightDiverge(c: Config): Boolean

  trait Whistle {
    def whistle(g: Graph): Boolean
    def |(w: Whistle) = (this, w) match {
      case (AnyWhistle(ws1), AnyWhistle(ws2)) => AnyWhistle(ws1 ++ ws2)
      case (AnyWhistle(ws1), w2) => AnyWhistle(ws1 :+ w2)
      case (w1, AnyWhistle(ws2)) => AnyWhistle(w1::ws2)
      case (w1, w2) => AnyWhistle(List(w1, w2))
    }
    def &(w: Whistle) = (this, w) match {
      case (AllWhistle(ws1), AllWhistle(ws2)) => AllWhistle(ws1 ++ ws2)
      case (AllWhistle(ws1), w2) => AllWhistle(ws1 :+ w2)
      case (w1, AllWhistle(ws2)) => AllWhistle(w1::ws2)
      case (w1, w2) => AllWhistle(List(w1, w2))
    }
  }

  case object NoWhistle extends Whistle {
    def whistle(g: Graph) = false
  }

  class ConfigWhistle(f: Config => Boolean) extends Whistle {
    def whistle(g: Graph) = g.current match {
      case None => false
      case Some(n) => f(n.config)
    }
  }

  // Whistle blows if the configuation might diverge
  case class MightDivergeWhistle() extends ConfigWhistle(mightDiverge _)

  case class DepthWhistle(maxDepth: Int) extends Whistle {
    def whistle(g: Graph) = g.depth > maxDepth
  }

  case class SizeWhistle(maxSize: Int) extends Whistle {
    def whistle(g: Graph) = g.size > maxSize
  }

  case class HEWhistle() extends Whistle {
    def whistle(g: Graph) = {
      g.current match {
        case Some(n) =>
          val nn = normalize(n.config)
          g.completeNodes.exists {
            n1 => isSmaller(normalize(n1.config), nn)
          }
        case None =>
          false
      }
    }
  }

  class FoldWhistle(ws: List[Whistle], f: (Boolean, Boolean) => Boolean) extends Whistle {
    def whistle(g: Graph) = {
      ws match {
        case Nil => false
        case w::ws => ws.foldLeft(w.whistle(g)) {
          case (result, w) => f(result, w.whistle(g))
        }
      }
    }
  }

  case class AllWhistle(ws: List[Whistle]) extends FoldWhistle(ws, _ && _)
  case class AnyWhistle(ws: List[Whistle]) extends FoldWhistle(ws, _ || _)
}
