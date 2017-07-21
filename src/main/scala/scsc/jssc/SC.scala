package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._

object SC {
  import Machine._
  import Continuations._
  import scsc.core.Residualization._
  import States._

  // remove unused assignments and variable declarations.
  def removeDeadCode(e: Exp): Exp = {
    var used: Set[Name] = Set()
    var changed = true

    while (changed) {
      changed = false

      object CollectUsed extends Rewriter {
        override def rewrite(e: Exp) = e match {
          case e @ Local(x) =>
            if (! (used contains x)) {
              changed = true
              used += x
            }
            e
          case e @ Residual(x) =>
            if (! (used contains x)) {
              changed = true
              used += x
            }
            e
          case e @ VarDef(x, _: Lambda) =>
            // don't recurse on variable definitions
            // unless the variable is already known to be used
            if (used contains x) {
              super.rewrite(e)
            }
            else {
              e
            }
          case e @ VarDef(x, _: Undefined) =>
            // don't recurse on variable definitions
            // unless the variable is already known to be used
            if (used contains x) {
              super.rewrite(e)
            }
            else {
              e
            }
          case e @ Assign(None, Residual(x), Local(y)) =>
            // FIXME: extend this to all pure expressions
            if (used contains x) {
              super.rewrite(e)
            }
            else {
              e
            }
          case e @ Assign(None, Residual(x), rhs) =>
            // Don't recurse on the LHS ... it's a def not a use!
            super.rewrite(rhs)
          case e =>
            super.rewrite(e)
        }
      }
      CollectUsed.rewrite(e)
    }

    object RemoveUnused extends Rewriter {
      override def rewrite(e: Exp) = super.rewrite(e) match {
        case e @ VarDef(x, _) =>
          if (used contains x) {
            e
          }
          else {
            Undefined()
          }
        case e @ Assign(None, Residual(x), Local(_)) =>
          if (used contains x) {
            e
          }
          else {
            Undefined()
          }
        case e @ Assign(None, Residual(x), rhs) =>
          if (used contains x) {
            e
          }
          else {
            rhs
          }
        case Seq(Undefined(), e) =>
          e
        case e =>
          e
      }
    }

    RemoveUnused.rewrite(e)
  }

  def alpha(e: Exp): Exp = {
    // rename residual variables in order of occurrence

    object Collector extends Rewriter {
      var map: Map[Name,Name] = Map()

      override def rewrite(e: Exp) = e match {
        case VarDef(x, _) =>
          // if (x.startsWith("_v")) {
          map += (x -> s"_v${map.size}")
          // }
          super.rewrite(e)
        case e =>
          super.rewrite(e)
      }
    }

    class Renamer(map: Map[Name, Name]) extends Rewriter {
      override def rewrite(e: Exp) = super.rewrite(e) match {
        case VarDef(x, b) =>
          map.get(x) match {
            case Some(y) => VarDef(y, b)
            case None => e
          }
        case e @ Local(x) =>
          map.get(x) match {
            case Some(y) => Local(y)
            case None => e
          }
        case e @ Residual(x) =>
          map.get(x) match {
            case Some(y) => Residual(y)
            case None => e
          }
        case e =>
          e
      }
    }

    Collector.rewrite(e)

    val e1 = new Renamer(Collector.map).rewrite(e)
    // println(s"alpha $e")
    // println(s"  --> $e1")
    e1
  }

  import scsc.core.Whistles
  import scsc.core.Interpreter
  import scsc.core.SC
  import States.State
  import scsc.core.Unsplit._

  object JSSuper extends SC[State] {
    def interp = JSInterp
    override val theMetaWhistle = MetaWhistles.DepthWhistle(100) | MetaWhistles.SplitDepthWhistle(20)
  }

  trait JSWhistles extends Whistles[State] {
    private type History = List[State]

    type NormalConfig = (Symbol, Exp, Int, Int, Cont)

    def normalize(s: State): NormalConfig = s match {
      case Ev(e, ρ, σ, k) => ('Ev, e, ρ.size, σ.size, k)
      case Co(e, σ, k) => ('Co, e, 0, σ.size, k)
      case Unwinding(jump, σ, k) => ('Unwinding, jump, 0, σ.size, k)
      case Rebuilt(e, σ, k) => ('Rebuilt, e, 0, σ.size, k)
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

  object JSInterp extends Interpreter[State] with JSWhistles {
    import States._

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
    // the state, so we actually try to convert the history to a Rebuilt.
    def rebuild(h: History): State = h match {
      case s::h => s
      case Nil => ???
    }

    def rollback(h: History): History = h match {
      case Rebuilt(_, _, _)::h => Nil
      case h => Split.rollback(h).getOrElse(Nil)
    }

    // split the current state, return Nil on failure
    def split(s: State): Option[(List[State], Unsplitter[State])] = {
      s.split
    }

    // Generalize, favoring the second state as the earlier state we're going to replace.
    def generalize(s1: State, s2: State): Option[State] = (s1, s2) match {
      case (Ev(e1, ρ1, σ1, k1), Ev(e2, ρ2, σ2, k2)) if e1 == e2 && k1 == k2 && ρ1 == ρ2 =>
        Some(Ev(e2, ρ2, σ2.merge(σ1, ρ2), k2))
      case _ => None
    }
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def eval(e: Exp, maxSteps: Int): Exp = {
    import scsc.js.PP

    val s0 = inject(e)

    JSSuper.supercompile(s0) match {
      case Some(s @ Stopped(v, σ)) =>
        Rebuilt(v, σ, Nil).residual
      case _ =>
        Undefined()
    }
  }

  //
  // def appendMemoizedFunctions(memo: JSDrive.Memo, e: Exp) = memo.foldRight(e) {
  //   case ((_, d), e) => Seq(d, e)
  // }

}
