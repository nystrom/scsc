package sc.js.sc

trait Stores extends sc.js.machine.Stores with sc.imp.sc.Stores {
  type MachineType <: Machine { type StoresType = Stores.this.type }
}
