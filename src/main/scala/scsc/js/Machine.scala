package scsc.js

import scsc.imp

trait Machine extends imp.Machine {
  type StatesType <: States { type MachineType = Machine.this.type }
  type EnvsType <: Envs { type MachineType = Machine.this.type }
  type StoresType <: Stores { type MachineType = Machine.this.type }
  type ContinuationsType <: Continuations { type MachineType = Machine.this.type }
  type TermsType <: Terms { type MachineType = Machine.this.type }

  object Parser extends Parser[this.type](this)
  object TreeWalk extends TreeWalk[this.type](this)
  object PP extends PP[this.type](this)

  object Globals extends Globals[this.type](this)

  // Set up the initial environment and store.
  // lazy val ρ0: envs.Env = Globals.ρ0
  // lazy val σ0: stores.Store = Globals.σ0

  lazy val ρ0: envs.Env = Globals.ρMin
  lazy val σ0: stores.Store = Globals.σMin
}
