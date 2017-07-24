package scsc.imp.sc

import scsc.imp

trait Continuations extends imp.Continuations with scsc.sc.Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }
}
