package sc.js.sc

trait States extends sc.js.machine.States with sc.imp.sc.States with Split with ReSemantics {
  this: sc.js.machine.Terms with Envs with Stores with sc.js.machine.Continuations =>
}
