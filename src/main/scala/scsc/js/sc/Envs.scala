package scsc.js.sc

trait Envs extends scsc.js.Envs with scsc.imp.sc.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
}
