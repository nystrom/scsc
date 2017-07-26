package sc.core.sc

trait Machine extends sc.core.machine.Machine {
  this: sc.core.machine.Terms with States with Envs with Stores with sc.core.machine.Continuations =>
}
