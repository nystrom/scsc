package sc.js.sc

trait Supercompiler extends Machine with sc.js.machine.Terms with States with Envs with Stores with sc.js.machine.Continuations with Split {
  machine =>

  import scala.collection.mutable.ListBuffer
  import sc.core.sc.Unsplit._

  object SC extends sc.core.sc.SC[State] {
    def interp = Interpreter
    override val theMetaWhistle = MetaWhistles.DepthWhistle(100) | MetaWhistles.SplitDepthWhistle(20)
  }

  object Interpreter extends sc.core.sc.Interpreter[State] with Whistles {
    private type History = List[State]

    // Step to the next state
    def step(s: State): Option[State] = machine.step(s)

    // Check if we should stop driving.
    def whistle(h: History): Boolean = theWhistle.blow(h)

    val theWhistle: Whistle = DepthWhistle(50) | (MightDivergeWhistle & TagbagWhistle)
    // val theWhistle: Whistle = DepthWhistle(100) | ((LoopWhistle() | RecursiveCallWhistle()) & HEWhistle())
    // val theWhistle: Whistle = DepthWhistle(100)
    // val theWhistle: Whistle = NoWhistle

    def isInstance(s1: State, s2: State): Boolean = {
      import org.bitbucket.inkytonik.kiama.util.Comparison.same
      same(s1, s2) || generalize(s1, s2).nonEmpty
    }

    // Fold the last element of the current history with a previous element, truncating
    // the history. The new last element of the history generalizes the old last element
    // and the previous element.
    // FIXME: other SC algorithms aren't restricted to folding with ancestors.
    // They can fold with any previously completed state (for instance in a memo table of bindings).
    def fold(h: History): Option[History] = h match {
      case Nil => None
      case s::h =>
        // This version of fold replaces a simple loop in the history with the root
        // of the history.
        object Generalizes {
          def unapply(h: History) = h match {
            case prev::tail => generalize(s, prev) map { _::tail }
            case _ => None
          }
        }

        h.tails collectFirst {
          case Generalizes(h) => h
        }
    }

    // Construct a new state from the current history.
    // This is not allowed to fail!
    // Since states in the history are all equivalent, we can just return
    // any state in the history, but clearly the first (newest) state is best.
    // However, the point is to be able to produce a residual term from
    // the state, so we actually try to convert the history to a Re.
    def rebuild(h: History): State = h match {
      case s::h => s
      case Nil => ???
    }

    def rollback(h: History): History = machine.rollback(h).getOrElse(Nil)

    // split the current state, return Nil on failure
    def split(s: State): Option[(List[State], Unsplitter[State])] = machine.split(s)

    // Generalize, favoring the second state as the earlier state we're going to replace.
    def generalize(s1: State, s2: State): Option[State] = (s1, s2) match {
      case (Ev(e1, ρ1, σ1, k1), Ev(e2, ρ2, σ2, k2)) if e1 == e2 && k1 == k2 && ρ1 == ρ2 =>
        Some(Ev(e2, ρ2, σ2.merge(σ1), k2))
      case _ => None
    }
  }

  trait Whistles extends sc.core.sc.Whistles[State] {
    private type History = List[State]

    type NormalConfig = (Symbol, Exp, Int, Int, Cont)

    def normalize(s: State): NormalConfig = s match {
      case Ev(e, ρ, σ, k) => ('Ev, e, ρ.size, σ.size, k)
      case Co(e, σ, k) => ('Co, e, 0, σ.size, k)
      case Unwinding(jump, σ, k) => ('Unwinding, jump, 0, σ.size, k)
      case Re(e, σ, k) => ('Re, e, 0, σ.size, k)
    }

    def mightDiverge(s: State) = s match {
      case Ev(Call(_, _), _, _, _) => true
      case Ev(NewCall(_, _), _, _, _) => true
      case Ev(While(_, _, _), _, _, _) => true
      case Ev(DoWhile(_, _, _), _, _, _) => true
      case Ev(For(_, _, _, _, _), _, _, _) => true
      case Ev(ForIn(_, _, _, _), _, _, _) => true
      case _ => false
    }

    def loop(s: State) = s match {
      case Ev(While(_, _, _), _, _, _) => true
      case Ev(DoWhile(_, _, _), _, _, _) => true
      case Ev(For(_, _, _, _, _), _, _, _) => true
      case Ev(ForIn(_, _, _, _), _, _, _) => true
      case _ => false
    }

    // Whistle blows if the configuation might diverge
    case class LoopWhistle() extends StateWhistle(loop _)

    case class RecursiveCallWhistle() extends Whistle {
      def blow(h: History) = h match {
        case Ev(c2: Call, _, _, _)::hist =>
          hist.exists {
            case Ev(c1: Call, _, _, _) => c1 == c2
            case _ => false
          }
        case Ev(c2: NewCall, _, _, _)::hist =>
          hist.exists {
            case Ev(c1: NewCall, _, _, _) => c1 == c2
            case _ => false
          }
        case _ => false
      }
    }
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def supercompile(e: Exp): Exp = {
    val s0 = machine.inject(e)

    SC.supercompile(s0) match {
      case Some(s1 @ Re(v, σ, Nil)) =>
        s1.residual
      case _ =>
        Undefined()
    }
  }
}
