package sc.imp.sc

trait Envs extends sc.imp.machine.Envs with sc.core.sc.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
}
