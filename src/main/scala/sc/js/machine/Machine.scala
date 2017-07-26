package sc.js.machine

trait Machine extends sc.imp.machine.Machine {
  this: Terms with States with Envs with Stores with Continuations =>

  val Globals: Globals[this.type]
}
