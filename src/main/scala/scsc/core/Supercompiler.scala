package scsc.core

// The supercompiler for language L is implemented as an interpreter of MetaStates.
// A State is the state of the L-interpreter.
// A MetaState is the state of the supercompiler and consists of a history
// of State and a MetaContinuation.
// The initial MetaState for State s is
// Drive(s, Nil, Nil)
// Drive(s, h, k)
// --> Drive(s'::Nil, s::h, k) if step(s) = s'
// --> Drive(s1, Nil, RunSplit(s2..sn, Nil, s, h)::k) if split(s) = [s1,..,sn]
// --> Drive(s', h', k) if opt(s, h) = (s', h')   // including fold?
// --> Drive(s', h', k) if fold(s, h) = (s', h')
// --> Rebuild(s', k) if rebuild(s, h) = s'
// ???
// Rebuild(s, RunSplit(s'::todo, done, s0, h0)::k)
// --> Drive(s', Nil, RunSplit(todo, done :+ s, s0, h0)::k)
// Rebuild(s, RunSplit(Nil, done, s0, h0)::k)
// --> Drive(reassemble(s0, done :+ s), h0, k)
// Rebuild(s, Nil) --> DONE
//
// Then in any state, we can do:
// whistle blows:
// Drive(s, h, k) --> Rebuild(rebuild(s, h), k)
// folding:
// Drive(s, h, k) --> Rebuild(fold(s, h), k)
trait Supercompiler[State] {
  private type History = List[State]

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

  sealed trait MetaFrame
  case class RunSplit(pending: List[State], complete: List[History], root: State, rootHistory: History) extends MetaFrame

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
    def isSmaller(child: MetaState, ancestor: MetaState): Boolean = child == ancestor
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

  val theMetaWhistle: MetaWhistles.Whistle = MetaWhistles.NoWhistle

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
              println(s"WHISTLE")
              Split(s, h, k)
            }
            else if (metaStop) {
              println(s"META WHISTLE")
              Split(s, h, k)
            }
            else {
              println(s"DRIVE OR SPLIT")
              interp.step(s) match {
                case Some(s1) => Drive(s1, s::h, k)
                case None => Split(s, h, k)
              }
            }
        }

      case Split(s, h, k) =>
        interp.split(s) match {
          case first::rest if ! metaStop =>
            Drive(first, Nil, RunSplit(rest, Nil, s, h)::k)
          case Nil =>
            Rebuild(s, h, k)
        }

      case Rebuild(s, h, RunSplit(next::pending, complete, s0, h0)::k) =>
        Drive(next, Nil, RunSplit(pending, complete :+ (s::h), s0, h0)::k)

      case Rebuild(s, h, RunSplit(Nil, complete, s0, h0)::k) =>
        interp.reassemble(s0, complete :+ (s::h)) match {
          case Left(first::rest) if ! metaStop =>
            // resplit
            Drive(first, Nil, RunSplit(rest, Nil, s0, h0)::k)
          case Left(_) =>
            // reassemble failed (or the meta whistle blew)
            // we need to just back out of the split entirely
            Rebuild(s0, h0, k)
          case Right(s1) =>
            // join successful, continue
            Drive(s1, h0, k)
        }
      case Rebuild(s, h, Nil) =>
        Done(interp.rebuild(s::h))
      case Done(s) =>
        // Done, return early
        return Done(s)
    }

    meta(next, ms::mss)
  }
}
