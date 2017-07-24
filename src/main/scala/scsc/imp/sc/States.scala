package scsc.imp.sc

import scsc.imp

trait States extends imp.States with scsc.sc.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  // Add split to the State interface
  trait State extends StateLike with Splittable

  trait Ev extends super.Ev with State
  trait Co extends super.Co with State
  trait Unwinding extends super.Unwinding with State

  trait Re extends State with ResidualLike

  val ReStep: RebuildStep[machine.type]

  def step(s: State) = s match {
    case s @ Re(e, sigma, k) =>
      ReStep.step(s)
  }
}
