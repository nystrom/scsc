package scsc.js.sc

import scsc.machine

trait Stores extends scsc.js.Stores with scsc.imp.sc.Stores {
  type MachineType <: Machine { type StoresType = Stores.this.type }
}
