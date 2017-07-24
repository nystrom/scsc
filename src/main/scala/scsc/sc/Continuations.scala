package scsc.sc

import scsc.machine

trait Continuations extends machine.Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }
}
