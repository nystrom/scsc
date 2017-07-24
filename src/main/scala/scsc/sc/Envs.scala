package scsc.sc

import scsc.machine

trait Envs extends machine.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
}
