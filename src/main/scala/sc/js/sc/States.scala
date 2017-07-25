package sc.js.sc

trait States extends sc.js.machine.States with sc.imp.sc.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  val EvSplit: EvSplit[machine.type]
  val CoSplit: CoSplit[machine.type]
  val Rollback: Rollback[machine.type]

  val ReStep: ResidualStep[machine.type]

  override def step(s: State) = super.step(s)
}
