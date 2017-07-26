package sc.js.sc

trait Machine extends sc.js.machine.Machine with sc.imp.sc.Machine {
  this: Terms with States with Envs with Stores with Continuations =>
}
