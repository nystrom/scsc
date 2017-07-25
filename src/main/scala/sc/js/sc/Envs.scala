package sc.js.sc

trait Envs extends sc.js.machine.Envs with sc.imp.sc.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
}
