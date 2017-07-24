package scsc.imp.sc

import scsc.imp

trait Envs extends imp.Envs with scsc.sc.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
}
