package sc.js.sc

trait Continuations extends sc.js.machine.Continuations with sc.imp.sc.Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }
}
