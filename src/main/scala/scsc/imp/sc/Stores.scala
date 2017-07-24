package scsc.imp.sc

import scsc.imp

trait Stores extends imp.Stores with scsc.sc.Stores {
  type MachineType <: Machine { type StoresType = Stores.this.type }
}
