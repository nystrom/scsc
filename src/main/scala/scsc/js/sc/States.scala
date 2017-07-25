package scsc.js.sc

import scsc.machine

trait States extends scsc.js.States with scsc.imp.sc.States {
  type MachineType <: Machine { type StatesType = States.this.type }

  val EvSplit: EvSplit[machine.type]
  val CoSplit: CoSplit[machine.type]
  val Rollback: Rollback[machine.type]

  val ReStep: ResidualStep[machine.type]

  override def step(s: State) = super.step(s)
}
