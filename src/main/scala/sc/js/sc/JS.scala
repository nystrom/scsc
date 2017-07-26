package sc.js.sc

import sc.js.machine.JSSemantics
import sc.js.machine.Terms

// concrete implementation of the machine
// this is just to ensure everything compiles
object JS extends Machine with States with Terms with Continuations with Envs with Stores with JSSemantics with Split {
  object Parser extends sc.js.syntax.Parser[this.type](this)
  object TreeWalk extends sc.js.syntax.TreeWalk[this.type](this)
  object Globals extends sc.js.machine.Globals[this.type](this)

  object PP extends sc.js.syntax.PP[this.type](this)
  object PPStates extends sc.imp.machine.PPStates[this.type](this)

  // Set up the initial environment and store.
  // lazy val ρ0: envs.Env = Globals.ρ0
  // lazy val σ0: stores.Store = Globals.σ0

  lazy val ρ0: Env = Globals.ρMin
  lazy val σ0: Store = Globals.σMin
}
