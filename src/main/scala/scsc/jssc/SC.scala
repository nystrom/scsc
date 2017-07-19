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

  trait Interpreter[State] {
    private type History = List[State]

    // Step to the next state
    def step(s: State): Option[State]

    // Check if we should stop driving.
    def whistle(h: List[State]): Boolean

    // Fold the last element of the current history with a previous element, truncating
    // the history. The new last element of the history generalizes the old last element
    // and the previous element.
    // FIXME: other SC algorithms aren't restricted to folding with ancestors.
    def fold(h: List[State]): Option[List[State]]

    // Construct a new state from the current history.
    // This is not allowed to fail!
    def rebuild(h: List[State]): State

    // Reassemble the root with new children.
    // This can either merge split states or generate a new split.
    // If a new split, then we resume driving, otherwise we rebuild.
    def reassemble(root: State, children: List[History]): Either[List[State], State]

    // split the current state, return Nil on failure
    def split(s: State): List[State]
  }

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
    case class Drive(state: State, history: History, k: MetaCont) extends MetaState
    case class Split(state: State, history: History, k: MetaCont) extends MetaState
    case class Rebuild(state: State, history: History, k: MetaCont) extends MetaState
    case class Done(state: State) extends MetaState

    sealed trait MetaFrame
    case class RunSplit(pending: List[State], complete: List[History], root: State, rootHistory: History) extends MetaFrame

    type MetaCont = List[MetaFrame]

    def interp: Interpreter[State]

    def supercompile(start: State): Option[State] = {
      val ms = Drive(start, Nil, Nil)
      meta(ms) match {
        case Done(s) => Some(s)
        case _ => None
      }
    }

    @scala.annotation.tailrec
    final def meta(ms: MetaState): MetaState = {
      println(s"META STATE $ms")
      val next = ms match {
        case Drive(s, h, k) =>
          interp.fold(s::h) match {
            case Some(s1::h1) =>
              println(s"FOLD")
              Drive(s1, h1, k)
            case None =>
              if (interp.whistle(s::h)) {
                println(s"WHISTLE")
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
            case first::rest => Drive(first, Nil, RunSplit(rest, Nil, s, h)::k)
            case Nil => Rebuild(s, h, k)
          }

        case Rebuild(s, h, RunSplit(next::pending, complete, s0, h0)::k) =>
          Drive(next, Nil, RunSplit(pending, complete :+ (s::h), s0, h0)::k)

        case Rebuild(s, h, RunSplit(Nil, complete, s0, h0)::k) =>
          interp.reassemble(s0, complete :+ (s::h)) match {
            case Left(first::rest) =>
              // resplit
              Drive(first, Nil, RunSplit(rest, Nil, s0, h0)::k)
            case Left(Nil) =>
              // reassemble failed
              // we need to just back out of the split entirely
              Rebuild(s0, h0, k)
            case Right(s1) =>
              // join successful
              Rebuild(s1, h0, k)
          }
        case Rebuild(s, h, Nil) =>
          Done(interp.rebuild(s::h))
        case Done(s) =>
          // Done, return early
          return Done(s)
      }

      meta(next)
    }
  }

  object JSSuper extends Supercompiler[States.State] {
    def interp = JSInterp
  }

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

  object JSSC extends scsc.core.SC {
    import States._

    type Config = State
    type NormalConfig = (Symbol, Exp, Cont)

    override def whistle: Whistle = DepthWhistle(1000)
    // override def whistle: Whistle = DepthWhistle(1000) | (MightDivergeWhistle() & HEWhistle())
    // override def whistle: Whistle = NoWhistle

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

    def step(s: State)(implicit context: Context): List[(State, EdgeKind)] = {
      assert(s == context.currentConfig.get)
      s.step.toList map { (_, Drive) }
    }

    def split(s: State)(implicit context: Context): List[(State, EdgeKind)] = {
      assert(s == context.currentConfig.get)
      val pos = context.currentPos.get
      Split.split(s) match {
        case ss => ss.zipWithIndex map {
          case (s1, i) => (s1, SplitAt(s, pos, i, ss.length))
        }
      }
    }

    def rebuilds(s: State)(implicit context: Context): List[State] = {
      assert(s == context.currentConfig.get)
      // Split.rebuild(s, context.currentPath).toList
      Nil
    }

    def rollbacks(s: State)(implicit context: Context): List[(Pos, State)] = {
      assert(s == context.currentConfig.get)
      Split.rollback(s, context.currentPath map { case (pos, st, _) => (pos, st) }).toList
    }

    def unsplit(rootState: State, splitStates: List[(Pos, State)])(implicit context: Context): List[State] = {
      val paths = splitStates map { case (pos, _) => context.pathToSplit(pos) }
      val sorted = paths.sortBy { case (path, i, n) => i }
      val pathsOnly = sorted map { _._1 }
      // Split.unsplit(rootState, pathsOnly)
      Nil
    }

    def generalize(child: State, ancestor: State)(implicit context: Context): Option[State] = None

    def halts(s: State)(implicit context: Context) = s match {
      case Halt(_, _, _) => true
      case Err(_, _) => true
      case _ => false
    }
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def eval(e: Exp, maxSteps: Int): Exp = {
    import scsc.js.PP
    import JSDrive.drive

    val s0 = inject(e)

    JSSuper.supercompile(s0) match {
      case Some(s @ Stopped(v, σ, φ)) =>
        Halt(v, σ, φ).residual
      case _ =>
        Undefined()
    }

/*
    drive(Nil, Nil, false)(s0) match {
      case (s @ Halt(v, σ, φ), memo) =>
        println(s"HALT SLOW ${PP.pretty(s.residual)}")
        return alpha(removeDeadCode(appendMemoizedFunctions(memo, s.residual)))
      case (Err(msg, s), _) =>
        println(s"FAIL $msg in $s")
        return Undefined()
      case (s, _) =>
        println(s"STUCK $s")
        return Undefined()
    }
    */
  }

  def appendMemoizedFunctions(memo: JSDrive.Memo, e: Exp) = memo.foldRight(e) {
    case ((_, d), e) => Seq(d, e)
  }

}
