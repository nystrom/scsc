package sc.js.sc

trait Machine extends sc.js.machine.Machine with sc.imp.sc.Machine {
  type StatesType <: States { type MachineType = Machine.this.type }
  type EnvsType <: Envs { type MachineType = Machine.this.type }
  type StoresType <: Stores { type MachineType = Machine.this.type }
  type ContinuationsType <: Continuations { type MachineType = Machine.this.type }
  type TermsType <: Terms { type MachineType = Machine.this.type }
}
