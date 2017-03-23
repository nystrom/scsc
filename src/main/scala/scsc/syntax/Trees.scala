package scsc.syntax

import scsc.syntax.LambdaSyntax._

object Trees {
  type Tree = ASTNode
  type Name = String

  implicit class AltImplicits(t: ASTNode) {
    def show: String = LambdaPrettyPrinter.show(t).replace("  ", " ")
  }

  implicit class ExpImplicits(e: Exp) {
    def isValue: Boolean = e match {
      case Num(_) => true
      case Lam(_, _) => true
      case Var(_) => false
      case Ctor(k, es) => es.forall(_.isValue)
      case Bin(_, _, _) => false
      case Neg(_) => false
      case Not(_) => false
      case App(_, _) => false
      case Case(_, _) => false
      case Let(_, _, _) => false
      case Letrec(_, _, _) => false
      case Residual(e) => true
      case Assign(x, e) => false
      case Seq(e1, e2) => false
    }

    def costZero: Boolean = e match {
      case Num(_) => true
      case Lam(_, _) => true
      case Ctor0(_) => true
      case Ctor1(k, es) => es.forall(_.costZero)
      case Var(x) => true
      case Residual(e) => e.costZero
      case _ => false
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

  // object Ctor {
  //   def apply(k: Name, es: List[Exp]): Exp = es.foldLeft(Ctor0(k): Exp) {
  //     case (f, a) => App(f, a)
  //   }
  //   def unapply(e: Exp): Option[(Name, List[Exp])] = e match {
  //     case Ctor0(k) => Some((k, Nil))
  //     case App(Ctor(k, es), e) => Some((k, es :+ e))
  //     case _ => None
  //   }
  // }

  object Ctor {
    def apply(k: Name, es: List[Exp]): Exp = es match {
      case Nil => Ctor0(k)
      case es => Ctor1(k, es)
    }
    def unapply(e: Exp): Option[(Name, List[Exp])] = e match {
      case Ctor0(k) => Some((k, Nil))
      case Ctor1(k, es) => Some((k, es))
      case _ => None
    }
  }

  val True = Ctor0("True")
  val False = Ctor0("False")

  def If(c: Exp, e1: Exp, e2: Exp) = {
    Case(e1, Alt(PCtor("True", Nil), e1)::
             Alt(PCtor("False", Nil), e2)::Nil)
  }

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
