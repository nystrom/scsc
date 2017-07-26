package sc.js.sc

trait States extends sc.js.machine.States with sc.imp.sc.States {
  this: sc.js.machine.Terms with Envs with Stores with Continuations with sc.js.machine.JSSemantics with Split =>
}
