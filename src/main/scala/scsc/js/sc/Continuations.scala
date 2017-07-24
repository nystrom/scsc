package scsc.js.sc

trait Continuations extends scsc.js.Continuations with scsc.imp.sc.Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }
}
