package sc.core.sc

import sc.core.machine

trait Continuations extends machine.Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }
}
