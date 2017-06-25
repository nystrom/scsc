package scsc.js

object TreeWalk {
  import Trees._

  trait Rewriter {
    def rewriteM(e: Exp): List[Exp] = {
      List(rewrite(e))
    }
    def rewriteO(e: Exp): Option[Exp] = {
      Some(rewrite(e))
    }
    final def rewrite(es: List[Exp]): List[Exp] = {
      es.flatMap { case e => rewriteM(e) }
    }
    final def rewrite(es: Option[Exp]): Option[Exp] = {
      es.flatMap { case e => rewriteO(e) }
    }

    def rewrite(e: Exp): Exp = e match {
      case Loc(address) =>
        Loc(address)
      case Residual(e) =>
        Residual(rewrite(e))
      case Unary(op, e) =>
        Unary(op, rewrite(e))
      case IncDec(op, e) =>
        IncDec(op, rewrite(e))
      case Delete(e) =>
        Delete(rewrite(e))
      case New(e) =>
        New(rewrite(e))
      case Typeof(e) =>
        Typeof(rewrite(e))
      case Void(e) =>
        Void(rewrite(e))
      case Assign(op, left, right) =>
        Assign(op, rewrite(left), rewrite(right))
      case Binary(op, left, right) =>
        Binary(op, rewrite(left), rewrite(right))
      case Access(base, prop) =>
        Access(rewrite(base), prop)
      case Block(es) =>
        Block(rewrite(es))
      case Break(label) =>
        Break(label)
      case Call(f, args) =>
        Call(rewrite(f), rewrite(args))
      case Case(test, body) =>
        Case(rewrite(test), rewrite(body))
      case Catch(ex, test, body) =>
        Catch(rewrite(ex), rewrite(test), rewrite(body))
      case Continue(label) =>
        Continue(label)
      case Empty() =>
        Empty()
      case Eval(e) =>
        Eval(rewrite(e))
      case For(init, test, modify, body) =>
        For(rewrite(init), rewrite(test), rewrite(modify), rewrite(body))
      case FunDef(name, params, body) =>
        FunDef(name, params, rewrite(body))
      case Lambda(params, body) =>
        Lambda(params, rewrite(body))
      case Ident(x) =>
        Ident(x)
      case IfThen(test, pass) =>
        IfThen(rewrite(test), rewrite(pass))
      case IfElse(test, pass, fail) =>
        IfElse(rewrite(test), rewrite(pass), rewrite(fail))
      case Index(a, i) =>
        Index(rewrite(a), rewrite(i))
      case Label(label, body) =>
        Label(label, rewrite(body))
      case ArrayLit(es) =>
        ArrayLit(rewrite(es))
      case Bool(v) =>
        Bool(v)
      case Num(v) =>
        Num(v)
      case StringLit(v) =>
        StringLit(v)
      case Null() =>
        Null()
      case Undefined() =>
        Undefined()
      case ObjectLit(es) =>
        ObjectLit(rewrite(es))
      case Property(k, v) =>
        Property(rewrite(k), rewrite(v))
      case Return(e) =>
        Return(rewrite(e))
      case Yield(e) =>
        Yield(rewrite(e))
      case Switch(e, cases) =>
        Switch(rewrite(e), rewrite(cases))
      case Cond(test, pass, fail) =>
        Cond(rewrite(test), rewrite(pass), rewrite(fail))
      case Throw(e) =>
        Throw(rewrite(e))
      case Try(e, catches, fin) =>
        Try(rewrite(e), rewrite(catches), rewrite(fin))
      case VarDef(x, init) =>
        VarDef(x, rewrite(init))
      case LetDef(x, init) =>
        LetDef(x, rewrite(init))
      case ConstDef(x, init) =>
        ConstDef(x, rewrite(init))
      case While(cond, body) =>
        While(rewrite(cond), rewrite(body))
      case DoWhile(body, cond) =>
        DoWhile(rewrite(body), rewrite(cond))
      case With(exp, body) =>
        With(rewrite(exp), rewrite(body))
    }
  }
}
