package sc.imp.machine

import sc.core.machine

trait Envs extends machine.Envs {
  type MachineType <: Machine { type EnvsType = Envs.this.type }

  import machine.terms.Name
  import machine.stores.Loc
  import scala.collection.immutable.SortedMap

  type Name = String

  type Env = SortedMap[Name, Loc]
  val ρempty = SortedMap()
}
