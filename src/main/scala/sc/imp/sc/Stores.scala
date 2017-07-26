package sc.imp.sc

import sc.imp.machine

trait Stores extends sc.imp.machine.Stores with sc.core.sc.Stores {
  this: Terms with Envs =>

  // TODO:
  // At this point, we run the machine in abstract interpretation mode
  // to simulate the store. See the AAM work of Van Horn and Might.
  def simulateStore(e: Exp)(σ: Store, ρ: Env) = σ
  def extendWithCond(test: Exp, σ: Store, ρ: Env, dir: Boolean) = σ

}
