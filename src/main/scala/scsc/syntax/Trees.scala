package scsc.syntax

import scala.collection.mutable.ListBuffer
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
import org.bitbucket.inkytonik.kiama.rewriting.Strategy
import org.bitbucket.inkytonik.kiama.util.{ParsingREPL, Positions, Profiler}
import scsc.syntax.LambdaSyntax._

object Trees {
  type Name = String

  implicit class IV(e: Exp) {
    def isValue: Boolean = e match {
      case Num(_) => true
      case Lam(_, _) => true
      case Var(_) => false
      case App(_, _) => false
      case Bin(_, _, _) => false
      case Neg(_) => false
      case Not(_) => false
      case Case(_, _) => false
      case Let(_, _, _) => false
      case Letrec(_, _, _) => false
      case Ctor(k, es) => es.forall(_.isValue)
      case Residual(e) => true
    }
  }

  sealed trait Operator
  case object OpOr extends Operator { override def toString = "||" }
  case object OpAnd extends Operator { override def toString = "&&" }
  case object OpEq extends Operator { override def toString = "==" }
  case object OpNe extends Operator { override def toString = "!=" }
  case object OpLt extends Operator { override def toString = "<" }
  case object OpLe extends Operator { override def toString = "<=" }
  case object OpGt extends Operator { override def toString = ">" }
  case object OpGe extends Operator { override def toString = ">=" }
  case object OpAdd extends Operator { override def toString = "+" }
  case object OpSub extends Operator { override def toString = "-" }
  case object OpMul extends Operator { override def toString = "*" }
  case object OpDiv extends Operator { override def toString = "/" }
  case object OpMod extends Operator { override def toString = "%" }

  object Bin {
    def unapply(e: Exp): Option[(Operator, Exp, Exp)] = e match {
      case Or(e1, e2) => Some((OpOr, e1, e2))
      case And(e1, e2) => Some((OpAnd, e1, e2))
      case Eq(e1, e2) => Some((OpEq, e1, e2))
      case Ne(e1, e2) => Some((OpNe, e1, e2))
      case Lt(e1, e2) => Some((OpLt, e1, e2))
      case Le(e1, e2) => Some((OpLe, e1, e2))
      case Gt(e1, e2) => Some((OpGt, e1, e2))
      case Ge(e1, e2) => Some((OpGe, e1, e2))
      case Add(e1, e2) => Some((OpAdd, e1, e2))
      case Sub(e1, e2) => Some((OpSub, e1, e2))
      case Mul(e1, e2) => Some((OpMul, e1, e2))
      case Div(e1, e2) => Some((OpDiv, e1, e2))
      case Mod(e1, e2) => Some((OpMod, e1, e2))
      case _ => None
    }

    def apply(op: Operator, e1: Exp, e2: Exp): Exp = op match {
      case OpOr  => Or(e1, e2)
      case OpAnd => And(e1, e2)
      case OpEq  => Eq(e1, e2)
      case OpNe  =>  Ne(e1, e2)
      case OpLt  =>  Lt(e1, e2)
      case OpLe  =>  Le(e1, e2)
      case OpGt  =>  Gt(e1, e2)
      case OpGe  =>  Ge(e1, e2)
      case OpAdd => Add(e1, e2)
      case OpSub => Sub(e1, e2)
      case OpMul => Mul(e1, e2)
      case OpDiv => Div(e1, e2)
      case OpMod => Mod(e1, e2)
    }
  }
}
object FreeVars {
  import Trees._

  def fv(t: Exp): Set[Name] = {
    t match {
      case o: Operator =>
        Set()
      case Num(_) =>
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
      case Ctor(c, ms) =>
        ms.flatMap { m => fv(m).toList }.toSet
      case Case(e, alts) =>
        fv(e) ++ alts.flatMap { case Alt(p, e) => fv(e) -- vars(p) }
      case Residual(e) =>
        fv(e)
    }
  }

  def vars(p: Pat): Set[Name] = p match {
    case PNum(_) => Set()
    case PCtor(_, ps) => ps.flatMap { case p => vars(p).toList }.toSet
    case PVar(x) => Set(x)
  }
}
