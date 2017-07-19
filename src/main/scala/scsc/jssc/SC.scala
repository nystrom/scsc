package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._

object SC {
  import Machine._
  import Continuations._
  import scsc.core.Residualization._
  import States._

  // Check for termination at these nodes.
  // In SCSC, we only checked at Local nodes, but here we need to check
  // loops also since we can have non-termination evaluating any variables.
  object CheckHistory {
    def unapply(e: Exp) = e match {
      case Local(x) => Some(e)
      case While(label, test, body) => Some(e)
      case DoWhile(label, body, test) => Some(e)
      case For(label, Empty(), test, iter, body) => Some(e)
      case ForEach(label, Empty(), test, iter, body) => Some(e)
      case ForIn(label, Empty(), iter, body) => Some(e)
      case _ => None
    }
  }

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

  import scsc.core.Interpreter
  import scsc.core.Supercompiler

  object JSSuper extends Supercompiler[States.State] {
    def interp = JSInterp
  }

  import scsc.core.Whistles

  trait JSWhistles extends Whistles[States.State] {
    type NormalConfig = (Symbol, Exp, Cont)

    def isInstance(s1: State, s2: State): Boolean = {
      object HE extends scsc.core.HE[NormalConfig]
      import HE._
      (s1 eq s2) || (normalize(s1) ≈ normalize(s2))
    }

    def isSmaller(child: State, ancestor: State): Boolean = {
      object HE extends scsc.core.HE[NormalConfig]
      import HE._
      (child eq ancestor) || (normalize(ancestor) ◁ normalize(child))
    }

    def mightDiverge(s: State) = s match {
      case Ev(Call(_, _), _, _, _, _) => true
      case Ev(NewCall(_, _), _, _, _, _) => true
      case Ev(While(_, _, _), _, _, _, _) => true
      case Ev(DoWhile(_, _, _), _, _, _, _) => true
      case Ev(For(_, _, _, _, _), _, _, _, _) => true
      case Ev(ForIn(_, _, _, _), _, _, _, _) => true
      case _ => false
    }

    def normalize(s: State): NormalConfig = s match {
      case Ev(e, ρ, σ, φ, k) => ('Ev, e, k)
      case Co(e, σ, φ, k) => ('Co, e, k)
      case Unwinding(jump, sigma, φ, k) => ('Unwinding, jump, k)
      case Rebuild(s) => normalize(s)
      case Halt(v, sigma, φ) => ('Halt, v, Nil)
      case Err(_, s) => normalize(s)
    }
  }

  object JSInterp extends Interpreter[States.State] with JSWhistles {
    import States._

    private type History = List[State]

    // Step to the next state
    def step(s: State): Option[State] = s.step

    // Check if we should stop driving.
    def whistle(h: History): Boolean = theWhistle.blow(h)

    // val theWhistle: Whistle = DepthWhistle(1000) | (MightDivergeWhistle() & HEWhistle())
    val theWhistle: Whistle = DepthWhistle(1000)
    // val theWhistle: Whistle = NoWhistle

    // Fold the last element of the current history with a previous element, truncating
    // the history. The new last element of the history generalizes the old last element
    // and the previous element.
    // FIXME: other SC algorithms aren't restricted to folding with ancestors.
    // They can fold with any previously completed state (for instance in a memo table of bindings).
    def fold(h: History): Option[History] = h match {
      case Nil => None
      case s::h =>
        h.span(prev => isInstance(s, prev)) match {
          case (Nil, h1) => None
          case (h1 :+ s1, h2) => generalize(s, s1).map(_::h2)
        }
    }

    // Construct a new state from the current history.
    // This is not allowed to fail!
    // We can always just return the oldest element of the history.
    // This means no evaluation happens, though.
    def rebuild(h: History): State = h match {
      case (s: Halt)::h => s
      case h => h.last
    }

    // Reassemble the root with new children.
    // This can either merge split states or generate a new split.
    // If a new split, then we resume driving, otherwise we rebuild.
    def reassemble(root: State, children: List[History]): Either[List[State], State] = Split.unsplit(root, children)

    // split the current state, return Nil on failure
    def split(s: State): List[State] = Split.split(s)

    def generalize(s1: State, s2: State): Option[State] = None
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def eval(e: Exp, maxSteps: Int): Exp = {
    import scsc.js.PP

    val s0 = inject(e)

    JSSuper.supercompile(s0) match {
      case Some(s @ Stopped(v, σ, φ)) =>
        Halt(v, σ, φ).residual
      case _ =>
        Undefined()
    }
  }
  //
  // def appendMemoizedFunctions(memo: JSDrive.Memo, e: Exp) = memo.foldRight(e) {
  //   case ((_, d), e) => Seq(d, e)
  // }

}
