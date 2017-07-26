package sc.imp.sc

trait Continuations extends sc.imp.machine.Continuations with sc.core.sc.Continuations {
  this: sc.imp.machine.Terms with Envs with Stores =>
}
