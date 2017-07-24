package scsc.js

import scsc.imp

trait Envs extends imp.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
}
