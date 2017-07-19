package scsc.core

trait Whistles[State] {
  private type History = List[State]

  def isInstance(s1: State, s2: State): Boolean
  def isSmaller(child: State, ancestor: State): Boolean

  // Return true if the configuration MIGHT diverge and should therefore
  // be tested using isSmaller.
  def mightDiverge(c: State): Boolean

  trait Whistle {
    def blow(h: History): Boolean
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
    def blow(h: History) = false
  }

  class StateWhistle(f: State => Boolean) extends Whistle {
    def blow(h: History) = h match {
      case Nil => false
      case s::_ => f(s)
    }
  }

  // Whistle blows if the configuation might diverge
  case class MightDivergeWhistle() extends StateWhistle(mightDiverge _)

  case class DepthWhistle(maxDepth: Int) extends Whistle {
    def blow(h: History) = h.length > maxDepth
  }

  case class HEWhistle() extends Whistle {
    def blow(h: History) = {
      h match {
        case Nil => false
        case s::h =>
          h.exists {
            prev => isSmaller(prev, s)
          }
      }
    }
  }

  class FoldWhistle(ws: List[Whistle], f: (Boolean, Boolean) => Boolean) extends Whistle {
    def blow(h: History) = {
      ws match {
        case Nil => false
        case w::ws => ws.foldLeft(w.blow(h)) {
          case (result, w) => f(result, w.blow(h))
        }
      }
    }
  }

  case class AllWhistle(ws: List[Whistle]) extends FoldWhistle(ws, _ && _)
  case class AnyWhistle(ws: List[Whistle]) extends FoldWhistle(ws, _ || _)
}
