package scsc.syntax

import scsc.syntax.LambdaSyntax._

object FreeVars {
  import Trees._

  def fv(t: Exp): Set[Name] = {
    t match {
      case Num(_) =>
        Set()
      case Loc(_) =>
        Set()
      case Var(x) =>
        Set(x)
      case Lam(x, e) =>
        fv(e) - x
      case App(m, n) =>
        fv(m) ++ fv(n)
      case Bin(_, m, n) =>
        fv(m) ++ fv(n)
      case Not(m) =>
        fv(m)
      case Neg(m) =>
        fv(m)
      case Let(x, m, n) =>
        fv(m) ++ (fv(n) - x)
      case Letrec(x, m, n) =>
        (fv(m) - x) ++ (fv(n) - x)
      case Ctor0(c) =>
        Set()
      case Ctor1(c, es) =>
        es.flatMap { case e => fv(e).toList }.toSet
      case Case(e, alts) =>
        fv(e) ++ alts.flatMap { case Alt(p, e) => fv(e) -- vars(p) }
      case Residual(e) =>
        fv(e)
    }
  }

  def vars(p: Pat): Set[Name] = p match {
    case PNum(_) => Set()
    case PLoc(_) => Set()
    case PCtor(_, ps) => ps.flatMap { case p => vars(p).toList }.toSet
    case PVar(x) => Set(x)
  }
}
