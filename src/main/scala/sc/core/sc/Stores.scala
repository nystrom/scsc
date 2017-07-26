package sc.core.sc

import sc.core.machine

trait Stores extends machine.Stores {
  this: Terms with Envs =>
}
