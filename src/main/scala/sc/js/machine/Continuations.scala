package sc.js.machine

trait Continuations extends sc.imp.machine.Continuations {
  this: Terms with Envs with Stores =>

  case class EvalProto(args: List[Exp], ρ: Env) extends Frame
  case class DoTypeof(ρ: Env) extends Frame

}
