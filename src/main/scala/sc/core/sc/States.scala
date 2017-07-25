package sc.core.sc

import sc.core.machine

trait States extends machine.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  import machine._
  import terms._
  import envs._
  import stores._
  import continuations._

  // Like a Continue, but with a residual expression in the focus.
  case class Re(residual: Term, σ: Store, k: List[Frame]) extends State

  // split a state. Like step we don't define it as a member of State
  import sc.core.sc.Unsplit.Unsplitter
  def split(s: State): Option[(List[State], Unsplitter[State])] = None
}
