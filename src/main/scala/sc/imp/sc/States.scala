package sc.imp.sc

trait States extends sc.imp.machine.States with sc.core.sc.States with Split with ReSemantics {
  this: sc.imp.machine.Terms with Envs with Stores with sc.imp.machine.Continuations =>
}
