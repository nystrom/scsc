package sc.js.sc

trait Machine extends sc.js.machine.Machine with sc.imp.sc.Machine {
  this: sc.js.machine.Terms with States with Envs with Stores with sc.js.machine.Continuations =>
}
