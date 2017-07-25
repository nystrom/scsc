package sc.js.machine

trait Envs extends sc.imp.machine.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
}
