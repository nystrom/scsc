package scsc.jssc

import scala.collection.mutable.ListBuffer
import scsc.js.Trees._
import scsc.js.TreeWalk._
import scsc.util.FreshVar

// This object defines the interpreter states and implements the step function
// for the JS interpreter.
object States {
  import Machine._
  import Continuations._
  import scsc.jssc.SC._
  import scsc.core.Residualization._
  import scsc.core.Unsplit._
  import CoStep._
  import EvStep._
  import RebuiltStep._
  import UnwindingStep._
  import CoSplit._
  import EvSplit._
  import RebuiltSplit._
  import UnwindingSplit._

  import org.bitbucket.inkytonik.kiama.util.Counter

  object CallCounter extends Counter {
    def apply(): Int = next()
  }

  // We implement the machine in "apply, eval, continue" form, following:
  // Olivier Danvy. An Analytical Approach to Program as Data Objects.
  // DSc thesis, Department of Computer Science, Aarhus University, 2006.

  // Ev dispatches on the expression, shifting the focus to a subexpression.
  // Co has a value in the focus and dispatches on the continuation.
  // Unwinding has a jump in the focus and dispatches on the continuation.
  //
  // The followings do not advance at all
  // Halt is done
  // Stuck wraps a state where no rule applies or where the whistle blue indicating evaluation should stop.

  // The step function can return either zero or one state.
  sealed trait State {
    def step: Option[State]
    def split: Option[(List[State], Unsplitter[State])]
  }

  sealed trait FinalState extends State {
    def step = None
    def split = None
  }

  object Stopped {
    def unapply(s: State): Option[(Exp, Store)] = s match {
      case Rebuilt(v2, σ2, k) => Some((v2, σ2))
      case Co(v2, σ2, k) => Some((v2, σ2))
      case Ev(e, ρ, σ, k) => Split.rebuildEv(e, ρ, σ, k).flatMap(unapply _)
      case Unwinding(jump, σ2, k) => Some((jump, σ2))
      case _ => None
    }
  }

  case class Ev(e: Exp, ρ: Env, σ: Store, k: Cont) extends State with EvStep with EvSplit {
    override def toString = s"""Ev
  e = $e
  k = ${k.mkString("[", "\n       ", "]")}"""
  //   override def toString = s"""Ev
  // e = $e
  // ρ = ${ρ.toVector.sortBy(_._1).mkString("{", "\n       ", "}")}
  // σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  // k = ${k.mkString("[", "\n       ", "]")}"""

  }

  // The Unwinding state just pops continuations until hitting a call or loop or catch.
  case class Unwinding(jump: Exp, σ: Store, k: Cont) extends State with UnwindingStep with UnwindingSplit {
  //   override def toString = s"""Unwinding
  // e = $jump
  // σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  // k = ${k.mkString("[", "\n       ", "]")}"""
    override def toString = s"""Unwinding
  e = $jump
  k = ${k.mkString("[", "\n       ", "]")}"""

  }

  case class Co(v: Val, σ: Store, k: Cont) extends State with CoStep with CoSplit {
  //   override def toString = s"""Co
  // v = $v
  // σ = ${σ.toVector.sortBy(_._1.address).mkString("{", "\n       ", "}")}
  // k = ${k.mkString("[", "\n       ", "]")}"""

    override def toString = s"""Co
  v = $v
  k = ${k.mkString("[", "\n       ", "]")}"""

  }

  // Like a Co, but with a rebuilt expression in the focus.
  case class Rebuilt(e: Exp, σ: Store, k: Cont) extends State with RebuiltStep with RebuiltSplit {
    def residual = e
  }

}
