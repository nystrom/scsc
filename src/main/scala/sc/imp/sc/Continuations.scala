package sc.imp.sc

import sc.imp.machine

trait Continuations extends sc.imp.machine.Continuations with sc.core.sc.Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }
}
