package scsc.js.sc

import scsc.machine

trait States extends scsc.js.States with scsc.imp.sc.States {
  type MachineType <: Machine { type StatesType = States.this.type }
}
