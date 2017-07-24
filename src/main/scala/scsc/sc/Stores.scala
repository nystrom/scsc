package scsc.sc

import scsc.machine

trait Stores extends machine.Stores {
  type MachineType <: Machine { type StoresType = Stores.this.type }
}
