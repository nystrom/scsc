package scsc.js

import scsc.imp

trait Continuations extends imp.Continuations {
  type MachineType <: Machine { type ContinuationsType = Continuations.this.type }

  import machine._
  import envs._
  import terms._
  import states._
  import stores._

  case class EvalProto(args: List[Exp], ρ: Env) extends Frame {
    override def step(s: Co) = s match {
      case Co(fun, σ, _::k) =>
        Some(Ev(Index(fun, StringLit("prototype")), ρ, σ, EvalMoreArgs(JSNary.NewCall, args, fun::Nil, ρ)::k))
      case _ =>
        super.step(s)
    }
  }

  case class DoTypeof() extends Frame {
    override def step(s: Co) = s match {
      case Co(v, σ, _::k) =>
        v match {
          case Num(v) => Some(Co(StringLit("number"), σ, k))
          case Bool(v) => Some(Co(StringLit("boolean"), σ, k))
          case StringLit(v) => Some(Co(StringLit("string"), σ, k))
          case Undefined() => Some(Co(StringLit("undefined"), σ, k))
          case Null() => Some(Co(StringLit("object"), σ, k))
          case Path(loc, path) =>
            σ.get(loc) match {
              case Some(BlobClosure(JSBlob(typeof, _, _, _), _)) =>
                Some(Co(StringLit(typeof), σ, k))
              case Some(ValueClosure(v)) =>
                Some(Co(v, σ, DoTypeof()::k))
              case Some(LocClosure(loc)) =>
                // The address of an object
                Some(Co(Path(loc, path), σ, DoTypeof()::k))
              case _ =>
                super.step(s)
            }
          case e =>
            super.step(s)
        }
      case _ =>
        super.step(s)
    }
  }
}
