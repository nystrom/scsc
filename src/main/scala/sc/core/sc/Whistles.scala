package sc.core.sc

trait Whistles[State] {
  private type History = List[State]

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

  def isInstance(s1: State, s2: State): Boolean

  // Return true if the configuration MIGHT diverge and should therefore
  // be tested using isSmaller.
  def mightDiverge(c: State): Boolean

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
  case object MightDivergeWhistle extends StateWhistle(mightDiverge _)

  case class DepthWhistle(maxDepth: Int) extends Whistle {
    def blow(h: History) = h.length > maxDepth
  }

  def tagOf(a: Any): Any = a match {
    case n: Int if n > 3 => 3
    case n: Int if n < -3 => -3
    case n: Int => n
    case n: Long if n > 3 => 3
    case n: Long if n < -3 => -3
    case n: Long => n
    case n: Float => 0.0
    case n: Double => 0.0
    case n: Char => n
    case n: String => ""
    case n: Boolean => n
    case n => n.getClass.getName
  }

  def tagbag(s: State) = {
    import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
    lazy val makeBag = collectl[Any] {
      case n => tagOf(n)
    }
    makeBag(s)
  }

  def size(s: State): Int = {
    import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
    count {
      case a => 1
    } (s)
  }

  case object TagbagWhistle extends Whistle {
    def isSmaller(s1: State, s2: State): Boolean = {
      import org.bitbucket.inkytonik.kiama.util.Comparison.same
      val bag1 = tagbag(s1)
      val bag2 = tagbag(s2)
      same(s1, s2) || (bag1.length < bag2.length && bag1.toSet == bag2.toSet)
    }

    def blow(h: History) = {
      h match {
        case Nil => false
        case s::h =>
          h.exists {
            prev =>
              val v = isSmaller(prev, s)
              if (v) println(s"""
$prev < $s
""")
              v
          }
      }
    }
  }

  class FoldWhistle(ws: List[Whistle], f: (Boolean, Boolean) => Boolean) extends Whistle {
    def blow(h: History) = {
      ws match {
        case Nil => false
        case w::ws =>
          println(s"Whistle $w says ${w.blow(h)}")
          ws.foldLeft(w.blow(h)) {
            case (result, w) =>
              println(s"Whistle $w says ${w.blow(h)}")
              f(result, w.blow(h))
          }
      }
    }
  }

  case class AllWhistle(ws: List[Whistle]) extends FoldWhistle(ws, _ && _)
  case class AnyWhistle(ws: List[Whistle]) extends FoldWhistle(ws, _ || _)
}
