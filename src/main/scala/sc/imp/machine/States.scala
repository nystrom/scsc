package sc.imp.machine

import sc.core.machine

trait States extends machine.States with Semantics {
  this: Terms with Envs with Stores with Continuations =>

  val PPStates: PPStates[this.type]

  implicit class PPDecorate(n: State) {
    def pretty: String = PPStates.pretty(n)
    def ugly: String = PPStates.ugly(n)
  }
}
