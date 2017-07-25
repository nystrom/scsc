package sc.js.machine

trait Machine extends sc.imp.machine.Machine {
  type StatesType <: States { type MachineType = Machine.this.type }
  type EnvsType <: Envs { type MachineType = Machine.this.type }
  type StoresType <: Stores { type MachineType = Machine.this.type }
  type ContinuationsType <: Continuations { type MachineType = Machine.this.type }
  type TermsType <: Terms { type MachineType = Machine.this.type }

  val Parser: Parser[this.type]
  val TreeWalk: TreeWalk[this.type]
  val Globals: Globals[this.type]
}
