package sc.imp.sc

trait States extends sc.imp.machine.States with sc.core.sc.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  type History = List[State]

  // Add split to the State interface
  abstract override def split(s: State) = s match {
    case s @ Ev(_, _, _, _) => EvSplit.split(s)
    case s @ Co(_, _, _) => CoSplit.split(s)
    case s @ Unwinding(_, _, _) => None
    case s @ Re(_, _, _) => None
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
