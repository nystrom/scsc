package sc.core.sc

// The supercompiler for language L is implemented as an interpreter of MetaStates.
// A State is the state of the L-interpreter.
// A MetaState is the state of the supercompiler and consists of a command, a history
// of State and a MetaContinuation.
trait SC[State] {
  sealed trait MetaState

  case class Drive(state: State, history: History, k: MetaCont) extends MetaState {
    override def toString = s"Drive($state, _, $k)"
  }
  case class Split(state: State, history: History, k: MetaCont) extends MetaState {
    override def toString = s"Split($state, $history, $k)"
  }
  case class Rebuild(state: State, history: History, k: MetaCont) extends MetaState {
    override def toString = s"Rebuild($state, _, $k)"
  }
  case class Done(state: State) extends MetaState

  import Unsplit._
  private type History = List[State]

  sealed trait MetaFrame
  case class RunSplit(pending: List[State], complete: List[History], root: State, rootHistory: History, unsplit: Unsplitter[State]) extends MetaFrame

  type MetaCont = List[MetaFrame]

  def interp: Interpreter[State]

  def supercompile(start: State): Option[State] = {
    val ms = Drive(start, Nil, Nil)
    meta(ms, Nil) match {
      case Done(s) => Some(s)
      case _ => None
    }
  }

  trait MetaWhistles extends Whistles[MetaState] {
    def isInstance(s1: MetaState, s2: MetaState): Boolean = s1 == s2
    def mightDiverge(ms: MetaState): Boolean = false

    case class SplitDepthWhistle(maxDepth: Int) extends Whistle {
      def blow(h: List[MetaState]) = h match {
        case Drive(_, _, k)::_ => k.length > maxDepth
        case Split(_, _, k)::_ => k.length > maxDepth
        case _ => false
      }
    }
  }

  object MetaWhistles extends MetaWhistles

  val theMetaWhistle: MetaWhistles.Whistle = MetaWhistles.SplitDepthWhistle(10) | MetaWhistles.TagbagWhistle

  def metaWhistle(mss: List[MetaState]): Boolean = theMetaWhistle.blow(mss)

  @scala.annotation.tailrec
  final def meta(ms: MetaState, mss: List[MetaState]): MetaState = {
    lazy val metaStop = metaWhistle(ms::mss)

    println(s"META STATE $ms")
    val next = ms match {
      case Drive(s, h, k) =>
        interp.fold(s::h) match {
          case Some(s1::h1) =>
            println(s"FOLD")
            // After folding, rebuild.
            Rebuild(s1, h1, k)
          case _ =>
            if (interp.whistle(s::h)) {
              println(s"WHISTLE: SPLIT")
              Split(s, h, k)
            }
            else if (metaStop) {
              println(s"META WHISTLE: SPLIT")
              Split(s, h, k)
            }
            else {
              println(s"DRIVE")
              interp.step(s) match {
                case Some(s1) =>
                  println(s"DRIVE TOOK A STEP")
                  Drive(s1, s::h, k)
                case None =>
                  println(s"DRIVE FAILED: SPLIT")
                  Split(s, h, k)
              }
            }
        }

      case Split(s, h, k) =>
        interp.split(s) match {
          case Some((first::rest, unsplit)) if ! metaStop =>
            println(s"SPLIT SUCCESS: DRIVE")
            Drive(first, Nil, RunSplit(rest, Nil, s, h, unsplit)::k)
          case _ =>
            println(s"SPLIT FAILED: REBUILD")
            Rebuild(s, h, k)
        }

      case Rebuild(s, h, RunSplit(next::pending, complete, s0, h0, unsplit)::k) =>
        println("REBUILD: DRIVE NEXT")
        Drive(next, Nil, RunSplit(pending, complete :+ (s::h), s0, h0, unsplit)::k)

      case Rebuild(s, h, RunSplit(Nil, complete, s0, h0, unsplit)::k) =>
        println("REBUILD COMPLETE: REASSEMBLE")
        unsplit(complete :+ (s::h)) match {
          case UnsplitOk(s1) =>
            println("REASSEMBLE SUCCESS: DRIVE")
            // join successful, continue
            Drive(s1, h0, k)
          case Resplit(first::rest, unsplit) if ! metaStop =>
            println("REASSEMBLE: RESPLIT")
            // resplit
            Drive(first, Nil, RunSplit(rest, Nil, s0, h0, unsplit)::k)
          case Resplit(states, unsplit) =>
            println("REASSEMBLE: RESPLIT META WHISTLE")
            // resplit
            Rebuild(s0, h0, k)
          case _ =>
            println("REASSEMBLE FAILED: REBUILD")
            // reassemble failed (or the meta whistle blew)
            // rollback the current history, causing a residualization
            interp.rollback(s::h) match {
              case s1::h1 =>
                println("ROLLBACK: DRIVE")
                Drive(s1, h1, k)
              case Nil =>
                println("ROLLBACK: POP SPLIT")
                Rebuild(s0, h0, k)
            }
        }

      // FIXME: need to cleanup the states here to avoid two calls to rollback
      case Rebuild(s, h, Nil) =>
        println("REBUILD: ROLLBACK")
        interp.rollback(s::h) match {
          case s1::h1 =>
            println("ROLLBACK: DRIVE")
            Drive(s1, h1, Nil)
          case Nil =>
            Done(s)
        }

      case Done(s) =>
        // Done, return early
        return Done(s)
    }

    meta(next, ms::mss)
  }
}
