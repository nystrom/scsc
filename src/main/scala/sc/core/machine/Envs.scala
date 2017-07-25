package sc.core.machine

trait Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
  val machine: MachineType

  import machine._
  import stores.Loc

  type Name

  type Env <: Map[Name, Loc]
  val ρempty: Env
}
