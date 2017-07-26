package sc.imp.machine

import sc.core.machine

trait Machine extends machine.Machine {
  this: Terms with States with Envs with Stores with Continuations =>
}
