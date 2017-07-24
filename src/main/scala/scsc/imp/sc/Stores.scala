package scsc.imp.sc

import scsc.imp

trait Stores extends imp.Stores with scsc.sc.Stores {
  type MachineType <: Machine { type StoresType = Stores.this.type }

  import machine._
  import terms._
  import envs._
  import stores._

  // TODO:
  // At this point, we run the machine in abstract interpretation mode
  // to simulate the store. See the AAM work of Van Horn and Might.
  def simulateStore(e: Exp)(σ: Store, ρ: Env) = σ
  def extendWithCond(test: Exp, σ: Store, ρ: Env, dir: Boolean) = σ

}
