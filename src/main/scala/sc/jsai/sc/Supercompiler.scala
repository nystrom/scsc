package sc.jsai.sc

// For Kiama to work correctly states cannot be defined as nested classes.
// Define them in a companion object instead.
object Supercompiler {

  import sc.core.sc.Unsplit._

  import notjs.syntax._
  import notjs.abstracted.domains._
  import notjs.abstracted.interpreter.{State => Σ}

  sealed trait State {
    def step: Option[State]
    def split: Option[(List[State], Unsplitter[State])]
  }

  case class RebuildState(s: Stmt) extends State {
    def step = None
    def split = None
  }

  case class WrappedState(ς: Σ) extends State {
    def step = ς.next.toList match {
      case Nil => None
      case ς::Nil => Some(WrappedState(ς))
      case ςs => None
    }

    def defaultMerge(ς: Σ, ςs: List[Σ]): Unsplitter[State] = {
      def unsplit(children: List[List[State]]): UnsplitResult[State] = {
        if (children.exists(_.isEmpty))
          UnsplitFail()
        else if (children.length != ςs.length)
          UnsplitFail()
        else {
          // (ςs zip (children.map(_.head)) map {
          //   case (ς, RebuildState(s)) =>
          //   case (ς, WrappedState(ς1)) =>
          // }
          UnsplitOk(WrappedState(ς))
        }
      }

      unsplit
    }

    def split = ς.next.toList match {
      case Nil => None
      case ς::Nil => None
      case ςs => Some((ςs.map(WrappedState), defaultMerge(ς, ςs)))
    }
  }


}

trait Supercompiler {
  import Supercompiler._

  import scala.collection.mutable.ListBuffer
  import scala.collection.immutable.{Seq => Sequence}

  import sc.core.sc.Unsplit._

  import notjs.abstracted.interpreter.{State => Σ}
  import notjs.translator.jsast._
  import notjs.abstracted.init._
  import notjs.syntax._
  import notjs.abstracted.domains._
  import notjs.abstracted.traces._
  import TraceHelper._

  object SC extends sc.core.sc.SC[State] {
    def interp = Interpreter
    override val theMetaWhistle = MetaWhistles.DepthWhistle(100) | MetaWhistles.SplitDepthWhistle(20)
  }

  // We use a trace that has infinite context-sensitivity and
  // infinite heap-sensitivity.

  // Flow-sensitive stack-based infinite-CFA with infinite-sensitive heap
  case class InfiniteCFA(pp: Int, tr: Sequence[Int]) extends SameTrace[InfiniteCFA] {

    // flow-sensitive
    def updateSame( s: Stmt ) =
      InfiniteCFA(s.id, tr)

    // the program point of the current trace is the caller site
    // push caller site to the call history
    def updateSame( ρ:Env, σ: Store, self: BValue, args:BValue, s:Stmt ) =
      InfiniteCFA(s.id, pp +: tr)

    def toAddr =
      IntsToBigInt(tr, pp)

    def makeAddr( x:Var ) =
      IntsToBigInt(tr, x.id)
  }

  object InfiniteCFA {
    def apply(): InfiniteCFA =
      InfiniteCFA(0, Sequence[Int]())
  }


  object Interpreter extends sc.core.sc.Interpreter[State] with Whistles {
    private type History = List[State]

    // Step to the next state
    def step(s: State): Option[State] = s.step

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
    // Since states in the history are all equivalent, we can just reutrn
    // any state in the history, but clearly the first (newest) state is best.
    // However, the point is to be able to produce a residual term from
    // the state, so we actually try to convert the history to a Re.
    def rebuild(h: History): State = h match {
      case s::h => s
      case Nil => ???
    }

    def rollback(h: History): History = Nil

    // split the current state, return Nil on failure
    def split(s: State): Option[(List[State], Unsplitter[State])] = s.split

    // Generalize, favoring the second state as the earlier state we're going to replace.
    def generalize(s1: State, s2: State): Option[State] = (s1, s2) match {
      case _ => None
    }
  }

  trait Whistles extends sc.core.sc.Whistles[State] {
    private type History = List[State]

    type NormalConfig = (Symbol, Term, Int, Int, KStack)

    def normalize(s: State): NormalConfig = s match {
      case WrappedState(Σ(t, ρ, σ, ß, κs, τ)) => ('State, t, 0, 0, κs)
      case RebuildState((s)) => ('Rebuild, s, 0, 0, KStack(Nil))
    }

    def mightDiverge(s: State) = s match {
      case WrappedState(Σ(StmtT(While(e,s)), ρ, σ, ß, κs, τ)) => true
      case WrappedState(Σ(StmtT(For(x, e, s)), ρ, σ, ß, κs, τ)) => true
      case WrappedState(Σ(StmtT(Newfun(x, m, n)), ρ, σ, ß, κs, τ)) => true
      case WrappedState(Σ(StmtT(New(x, e1, e2)), ρ, σ, ß, κs, τ)) => true
      case WrappedState(Σ(StmtT(Call(x, e1, e2, e3)), ρ, σ, ß, κs, τ)) => true
      case _ => false
    }

    def loop(s: State) = s match {
      case WrappedState(Σ(StmtT(While(e,s)), ρ, σ, ß, κs, τ)) => true
      case WrappedState(Σ(StmtT(For(x, e, s)), ρ, σ, ß, κs, τ)) => true
      case _ => false
    }

    // Whistle blows if the configuation might diverge
    case class LoopWhistle() extends StateWhistle(loop _)
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def supercompile(ast: Stmt): Option[Stmt] = {
    val initτ = InfiniteCFA()
    val initς = Init.initState( ast, initτ )

    SC.supercompile(WrappedState(initς)) match {
      case Some(WrappedState(Σ(StmtT(s), ρ, σ, ß, κs, τ))) => Some(s)
      case Some(WrappedState(Σ(_, _, _, _, _, _))) => None
      case Some(RebuildState(s)) => Some(s)
      case None => None
    }
  }
}
