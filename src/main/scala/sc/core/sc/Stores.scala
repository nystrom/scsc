package sc.core.sc

import sc.core.machine

trait Stores extends machine.Stores {
  type MachineType <: Machine { type StoresType = Stores.this.type }
}
