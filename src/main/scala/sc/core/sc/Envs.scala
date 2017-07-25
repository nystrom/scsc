package sc.core.sc

import sc.core.machine

trait Envs extends machine.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
}
