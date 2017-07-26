package sc.core.machine

trait Envs {
  this: Stores =>

  type Name

  type Env <: Map[Name, Loc]
  val ρempty: Env
}
