package scsc.js

class TreeWalk[M <: Machine](val machine: M) {
  import machine.terms._

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
      case Prim(name) =>
        Prim(name)
      case Path(address, path) =>
        Path(address, rewrite(path))
      case Residual(x) =>
        Residual(x)
      case Unary(op, e) =>
        Unary(op, rewrite(e))
      case IncDec(op, e) =>
        IncDec(op, rewrite(e))
      case Delete(e) =>
        Delete(rewrite(e))
      case Typeof(e) =>
        Typeof(rewrite(e))
      case Void(e) =>
        Void(rewrite(e))
      case Assign(op, left, right) =>
        Assign(op, rewrite(left), rewrite(right))
      case Binary(op, left, right) =>
        Binary(op, rewrite(left), rewrite(right))
      case Seq(e1, e2) =>
        Seq(rewrite(e1), rewrite(e2))
      case Break(label) =>
        Break(label)
      case Call(f, args) =>
        Call(rewrite(f), rewrite(args))
      case NewCall(f, args) =>
        NewCall(rewrite(f), rewrite(args))
      case Case(test, body) =>
        Case(rewrite(test), rewrite(body))
      case Catch(ex, test, body) =>
        Catch(ex, rewrite(test), rewrite(body))
      case Continue(label) =>
        Continue(label)
      case Empty() =>
        Empty()
      case For(label, init, test, modify, body) =>
        For(label, rewrite(init), rewrite(test), rewrite(modify), rewrite(body))
      case ForIn(label, init, modify, body) =>
        ForIn(label, rewrite(init), rewrite(modify), rewrite(body))
      case ForEach(label, init, test, modify, body) =>
        ForEach(label, rewrite(init), rewrite(test), rewrite(modify), rewrite(body))
      case Lambda(params, body) =>
        Lambda(params, rewrite(body))
      case Scope(body) =>
        Scope(rewrite(body))
      case Local(x) =>
        Local(x)
      case IfElse(test, pass, fail) =>
        IfElse(rewrite(test), rewrite(pass), rewrite(fail))
      case Index(a, i) =>
        Index(rewrite(a), rewrite(i))
      case ArrayLit(es) =>
        ArrayLit(rewrite(es))
      case Bool(v) =>
        Bool(v)
      case Num(v) =>
        Num(v)
      case StringLit(v) =>
        StringLit(v)
      case XML(v) =>
        XML(v)
      case Regex(v, opts) =>
        Regex(v, opts)
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
      case TryCatch(e, catches) =>
        TryCatch(rewrite(e), rewrite(catches))
      case TryFinally(e, fin) =>
        TryFinally(rewrite(e), rewrite(fin))
      case VarDef(x, init) =>
        VarDef(x, rewrite(init))
      case While(label, cond, body) =>
        While(label, rewrite(cond), rewrite(body))
      case DoWhile(label, body, cond) =>
        DoWhile(label, rewrite(body), rewrite(cond))
      case With(exp, body) =>
        With(rewrite(exp), rewrite(body))

      // case Loc(address) =>
      //   Loc(address)
      // case FunObject(typeof, proto, params, body, props) =>
      //   FunObject(typeof, rewrite(proto), params, rewrite(body), props map { case (x, e) => (x, rewrite(e).asInstanceOf[Loc]) })
    }
  }
}
