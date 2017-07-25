package scsc.sc

import scsc.machine

trait States extends machine.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  import machine._
  import terms._
  import envs._
  import stores._
  import continuations._

  // Like a Continue, but with a residual expression in the focus.
  trait ResidualLike extends StateLike {
    def residual: Term
    def σ: Store
    def k: List[Frame]
  }

  type Re <: State with ResidualLike
  val Re: ResidualFactory
  trait ResidualFactory {
    def apply(focus: Term, σ: Store, k: Cont): Re
    def unapply(s: Re): Option[(Term, Store, Cont)]
  }

  import scsc.core.Unsplit.Unsplitter

  def split(s: State): Option[(List[State], Unsplitter[State])] = None

  // Mixin to States
  trait Splittable {
    def split: Option[(List[State], Unsplitter[State])]
  }

  type State <: StateLike with Splittable
}
