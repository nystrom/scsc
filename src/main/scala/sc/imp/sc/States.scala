package sc.imp.sc

trait States extends sc.imp.machine.States with sc.core.sc.States {
  this: Terms with Envs with Stores with Continuations with Split =>
}
