package scsc.machine

trait Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }
  val machine: MachineType

  import machine._
  import terms.Name
  import stores.Loc

  type Env <: Map[Name, Loc]
  val ρempty: Env
}
