package sc.imp.machine

// concrete implementation of the machine
// this is just to ensure everything compiles
object Imp extends Machine with Terms with States with Envs with Stores with Continuations {
  val ρ0 = ρempty
  val σ0 = σempty

  def doCall(op: Operator, operands: List[Value], ρ: Env, σ: Store, k: Cont): Option[State] = None

  def evalUnaryOp(op: Operator, v: Value): Option[Value] = None
  def evalBinaryShortCircuitOp(op: Operator, v1: Value): Option[Value] = None
  def evalBinaryOp(op: Operator, v1: Value, v2: Value): Option[Value] = None

  def evalArrayOp(op: Operator, array: Value, index: Value, σ: Store): Option[(Value, Store)] = None

  def evalPredicate(v: Value): Option[Boolean] = None

  def addDeclarations(e: Exp, ρ: Env, σ: Store): (List[Exp], Env, Store) = (Nil, ρ, σ)

  object Loop extends Loop

  object PP extends sc.imp.syntax.PP[this.type](this)
  object PPStates extends PPStates[this.type](this)
}
