package sc.imp.machine

import sc.core.machine

trait Envs extends machine.Envs {
  this: Stores =>
  
  import scala.collection.immutable.SortedMap

  type Name = String

  type Env = SortedMap[Name, Loc]
  val ρempty = SortedMap()
}
