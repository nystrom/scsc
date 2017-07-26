package sc.imp.sc

trait Machine extends sc.imp.machine.Machine with sc.core.sc.Machine {
  this: Terms with States with Envs with Stores with Continuations =>
}
