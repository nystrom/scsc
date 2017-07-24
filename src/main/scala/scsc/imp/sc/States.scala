package scsc.imp.sc

import scsc.imp

trait States extends imp.States with scsc.sc.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  type History = List[State]

  // Add split to the State interface
  trait State extends StateLike with Splittable

  trait Ev extends super.Ev with State {
    def split = EvSplit.split(this)
  }
  trait Co extends super.Co with State {
    def split = CoSplit.split(this)
  }
  trait Unwinding extends super.Unwinding with State {
    def split = None
  }

  trait Re extends State with ResidualLike {
    def split = None
  }

  val EvSplit: EvSplit[machine.type]
  val CoSplit: CoSplit[machine.type]
  val Rollback: Rollback[machine.type]

  abstract override def step(s: State): Option[State] = s match {
    case s: Re =>
      ReStep.step(s)
    case s =>
      super.step(s)
  }

  val ReStep: ResidualStep[machine.type]
}
