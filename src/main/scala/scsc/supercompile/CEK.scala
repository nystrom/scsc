package scsc.supercompile

import scala.collection.mutable.ListBuffer
import org.bitbucket.inkytonik.kiama.util.{REPL, REPLConfig, Source, Console, Positions}
import scsc.syntax.LambdaPrettyPrinter
import scsc.syntax.LambdaSyntax._
import scsc.syntax.Trees._
import scsc.syntax.FreeVars._

// Issues:
// - residualization as operations on residual values. Free variables don't work!
//   - or rather, they work when they're free in the top-level expression but not
//     when they're free elsewhere, need to ensure the let for the variable is preserved.
//     But, this doesn't happen because we're already past the point of deciding to reify the let... it's not in the cont anymore
//     So: _always_ add the rebuild-let continuation, but don't reify unless the variable
//     is free in e1 or e2.
// - termination -- detecting folding. when folded, need to residualize, which is broken
// - termination -- detecting embedding. implementing generalization
// - distillation -- detects when a LTS is embedded in another, not when a state is embedded
//                -- an LTS is the entire (infinite) evaluation of the an expression
//                -- so, is the _history_ embedded in ... what?

// Distillation: is the current history embedded in an earlier history
// Distillation works on subtrees of the LTS.


// We start with a CEK machine for the lambda calculus.
object CEK {

  // The state of the CEK machine:
  case class Σ(c: Exp, e: Env, s: Store, k: Cont) {
    override def toString = s"Σ(e = ${LambdaPrettyPrinter.show(c)}, ρ = $e, σ = $s, k = $k)"
  }

  type St = Σ

  // Inject a term into the machine.
  def inject(e: Exp): St = Σ(e, ρ0, σ0, Done)

  ////////////////////////////////////////////////////////////////
  // ENVIRONMENTS
  ////////////////////////////////////////////////////////////////

  // In the CEK machine, environments map to closures.

  // In the CESK machine, environments map names to values (locations)
  // and the store maps locations to closures.
  case class Closure(e: Exp, ρ: Env) {
    override def toString = s"Closure(${LambdaPrettyPrinter.show(e)}, $ρ)"
  }

  val ρ0: Env = MapEnv(Map())

  trait Env {
    def get(x: Name): Option[Closure]
    def add(x: Name, v: Exp, ρ: Env): Env
    def addrec(x: Name, v: Exp): Env
  }
  case class MapEnv(table: Map[Name, Closure]) extends Env {
    override def toString = table.toString

    def get(x: Name): Option[Closure] = table.get(x).map {
      case Closure(v, SelfEnv) => Closure(v, this)
      case Closure(v, ρ) => Closure(v, ρ)
    }
    def add(x: Name, v: Exp, ρ: Env) = v match {
      case v if fv(v).isEmpty => MapEnv(table + (x -> Closure(v, MapEnv(Map()))))
      case v => MapEnv(table + (x -> Closure(v, ρ)))
    }
    def addrec(x: Name, v: Exp) = v match {
      case v if fv(v).isEmpty => MapEnv(table + (x -> Closure(v, MapEnv(Map()))))
      case v => MapEnv(table + (x -> Closure(v, SelfEnv)))
    }
  }
  case object SelfEnv extends Env {
    override def toString = "self"

    def get(x: Name): Option[Closure] = None
    def add(x: Name, v: Exp, ρ: Env) = throw new RuntimeException("illegal cycle")
    def addrec(x: Name, v: Exp) = throw new RuntimeException("illegal cycle")
  }

  ////////////////////////////////////////////////////////////////
  // STORES
  ////////////////////////////////////////////////////////////////

  type Loc = Int
  type Store = Map[Loc, Closure]

  val σ0: Store = Map()

  def mergeStores(σ1: Store, σ2: Store): Store = {
    if (σ1 eq σ2) {
      return σ1
    }

    import scala.collection.mutable.MapBuilder
    val σnew: MapBuilder[Loc, Closure, Store] = new MapBuilder(σ0)
    for ((loc1, v1) <- σ1) {
      σ2.get(loc1) match {
        case Some(v2) if v1 == v2 =>
          σnew += ((loc1, v2))
        case None =>
      }
    }
    σnew.result
  }

  ////////////////////////////////////////////////////////////////
  // CONTINUATIONS
  ////////////////////////////////////////////////////////////////

  // Here are the standard CEK continuations + a failure continuation
  sealed trait Cont extends Product
  case object Done extends Cont {
    override def toString = "∅"
  }
  case class EvalArg(arg: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"☐ ${LambdaPrettyPrinter.show(arg)} then $k"
  }
  case class Call(funValue: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"${LambdaPrettyPrinter.show(funValue)} ☐ then $k"
  }
  case class Fail(s: String) extends Cont {
    override def toString = s"FAIL($s)"
  }

  // Extensions:
  // Binary operators.
  case class OpRight(op: Operator, e2: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"☐ $op ${LambdaPrettyPrinter.show(e2)} then $k"
  }
  case class EvalOp(op: Operator, v1: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"${LambdaPrettyPrinter.show(v1)} $op ☐ then $k"
  }

  // Constructors.
  case class EvalCtorArgs(n: Name, argsToCompute: List[Exp], argsComputed: List[Exp], ρ: Env, k: Cont) extends Cont {
    override def toString = s"($n ${argsComputed.reverse.mkString(" ")} ☐ ${argsToCompute.mkString(" ")}) then $k"
  }

  // Let
  case class LetCont(x: Name, e: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"(let $x = ☐ in ${LambdaPrettyPrinter.show(e)}) then $k"
  }

  // Let
  case class LetrecCont(x: Name, e: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"(letrec $x = ☐ in ${LambdaPrettyPrinter.show(e)}) then $k"
  }

  // Case expressions
  case class EvalCase(alts: List[Alt], ρ: Env, k: Cont) extends Cont {
    override def toString = s"(case ☐ of ${alts.mkString(" | ")}) then $k"
  }
  case class EvalAlts(alts: List[Alt], ρ: Env, k: Cont) extends Cont {
    override def toString = s"(case ☐ of ${alts.mkString(" | ")}) then $k"
  }

  // Reificiation
  case class RebuildLet(x: Name, e: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"«let $x = ${LambdaPrettyPrinter.show(e)} in ☐» then $k"
  }
  case class RebuildLetrec(x: Name, e: Exp, ρ: Env, k: Cont) extends Cont {
    override def toString = s"«letrec $x = ${LambdaPrettyPrinter.show(e)} in ☐» then $k"
  }
  case class RebuildCase(alts: List[Alt], altsPrime: List[Alt], ρ: Env, σOpt: Option[Store], k: Cont) extends Cont {
    override def toString = s"«case ☐ of ${(altsPrime.reverse ++ alts).mkString(" | ")}» then $k"
  }
  case class RebuildAlt(e: Exp, p: Pat, alts: List[Alt], altsPrime: List[Alt], ρ: Env, k: Cont) extends Cont {
    override def toString = (alts, altsPrime) match {
      case (Nil, Nil) =>
        s"«case ${LambdaPrettyPrinter.show(e)} of $p -> ☐» then $k"
      case (alts, Nil) =>
        s"«case ${LambdaPrettyPrinter.show(e)} of $p -> ☐ | ${alts.mkString(" | ")}» then $k"
      case (Nil, altsPrime) =>
        s"«case ${LambdaPrettyPrinter.show(e)} of ${altsPrime.reverse.mkString(" | ")} | $p -> ☐» then $k"
      case (alts, altsPrime) =>
        s"«case ${LambdaPrettyPrinter.show(e)} of ${altsPrime.reverse.mkString(" | ")} | $p -> ☐ | ${alts.mkString(" | ")}» then $k"
    }
  }

  // Pattern matching, extended with residual values.
  def matchPat(v: Exp, p: Pat, ρ: Env): Option[Env] = (v, p) match {
    case (v, PVar(x)) => Some(ρ.add(x, v, ρ))
    case (Num(n1), PNum(n2)) if n1 != n2 => None
    case (Num(n1), PNum(n2)) => Some(ρ)
    case (Ctor(n1, _), PCtor(n2, _)) if n1 != n2 => None
    case (Ctor(n1, Nil), PCtor(n2, Nil)) => Some(ρ)
    case (Ctor(n1, a::as), PCtor(n2, q::qs)) =>
      for {
        ρ1 <- matchPat(a, q, ρ)
        ρ2 <- matchPat(Ctor(n1, as), PCtor(n2, qs), ρ1)
      } yield ρ2
    case (Residual(Ctor(n1, _)), PCtor(n2, _)) if n1 != n2 => None
    case (Residual(Ctor(n1, Nil)), PCtor(n2, Nil)) => Some(ρ)
    case (Residual(Ctor(n1, a::as)), PCtor(n2, q::qs)) =>
      for {
        ρ1 <- matchPat(reify(a), q, ρ)
        ρ2 <- matchPat(Residual(Ctor(n1, as)), PCtor(n2, qs), ρ1)
      } yield ρ2
    // Any residual value _might_ match the pattern.
    // TODO: check the type and other constraints.
    // Just return the original environment without binding the variables
    // in the pattern.
    case (Residual(e), p) => Some(ρ)
    case _ => None
  }

  // Partial evaluation is implemented as follows:
  // We start with normal CEK-style evaluation.

  // We extend the term syntax with values for residual terms.
  // The machine must handle evaluation over residuals, which are considered values.
  // We don't need to write a function to extract the residual term, it just gets
  // computed by running the machine to the Done continuation.

  // Extending with constraints:
  // When we see Σ(Residual(e), ρ, k)
  // Lookup e as a constraint term in ρ. If we can determine its value, done!

  def costZero(e: Exp): Boolean = e match {
    case Num(_) => true
    case Lam(_, _) => true
    case Ctor(k, es) => es.forall(costZero)
    case Var(x) => true
    case _ => false
  }

  def reify(e: Exp): Exp = e match {
    case Num(n) => Num(n)
    case Lam(x, e) => Lam(x, unreify(e))
    case Ctor(k, es) if costZero(e) && fv(e).isEmpty => e
    case Residual(e) => reify(e)
    case Var(x) => Residual(Var(x))
    case App(e1, e2) => Residual(App(unreify(e1), unreify(e2)))
    case Bin(op, e1, e2) => Residual(Bin(op, unreify(e1), unreify(e2)))
    case Neg(e) => Residual(Neg(unreify(e)))
    case Not(e) => Residual(Not(unreify(e)))
    case Ctor(k, es) => Residual(Ctor(k, es.map(unreify)))
    case Let(x, e1, e2) => Residual(Let(x, unreify(e1), unreify(e2)))
    case Letrec(x, e1, e2) => Residual(Letrec(x, unreify(e1), unreify(e2)))
    case Case(e, alts) => Residual(Case(unreify(e), alts.map { case Alt(p, e) => Alt(p, unreify(e)) }))
  }

  def strongReify(e: Exp): Exp = Residual(unreify(e))

  def unreify(e: Exp): Exp = e match {
    case Num(n) => Num(n)
    case Lam(x, e) => Lam(x, unreify(e))
    case Residual(e) => unreify(e)
    case Var(x) => Var(x)
    case App(e1, e2) => App(unreify(e1), unreify(e2))
    case Bin(op, e1, e2) => Bin(op, unreify(e1), unreify(e2))
    case Neg(e) => Neg(unreify(e))
    case Not(e) => Not(unreify(e))
    case Ctor(k, es) => Ctor(k, es.map(unreify))
    case Let(x, e1, e2) => Let(x, unreify(e1), unreify(e2))
    case Letrec(x, e1, e2) => Letrec(x, unreify(e1), unreify(e2))
    case Case(e, alts) => Case(unreify(e), alts.map { case Alt(p, e) => Alt(p, unreify(e)) })
  }

  def step(s: St): St = s match {
    ////////////////////////////////////////////////////////////////
    // Variables. Just lookup the value. If not present, residualize.
    ////////////////////////////////////////////////////////////////
    case Σ(Var(x), ρ, σ, k) => ρ.get(x) match {
      case Some(Closure(e1, ρ1)) =>
        Σ(e1, ρ1, σ, k)
      case None =>
        println(s"variable $x not found... residualizing")
        Σ(reify(Var(x)), ρ, σ, k)
    }

    ////////////////////////////////////////////////////////////////
    // Let.
    ////////////////////////////////////////////////////////////////

    case Σ(Let(x, e1, e2), ρ, σ, k) =>
      Σ(e1, ρ, σ, LetCont(x, e2, ρ, k))

    // Always rebuild the let.
    case Σ(v, ρ, σ, LetCont(x, e2, ρ1, k)) if v.isValue && ! costZero(v) =>
      // Extend the environment with x.
      lazy val ρ2: Env = ρ1.add(x, reify(Var(x)), ρ)
      Σ(e2, ρ2, σ, RebuildLet(x, v, ρ1, k))

    // Always rebuild the let.
    case Σ(v, ρ, σ, LetCont(x, e2, ρ1, k)) if v.isValue =>
      // Extend the environment with x.
      lazy val ρ2: Env = ρ1.add(x, v, ρ1)
      Σ(e2, ρ2, σ, RebuildLet(x, v, ρ1, k))

    case Σ(Letrec(x, e1, e2), ρ, σ, k) =>
      lazy val ρ1: Env = ρ.addrec(x, e1)
      Σ(e1, ρ1, σ, LetrecCont(x, e2, ρ, k))

    // Always rebuild the let.
    case Σ(v, ρ, σ, LetrecCont(x, e2, ρ1, k)) if v.isValue && ! costZero(v) =>
      // Extend the environment with x.
      lazy val ρ2: Env = ρ1.addrec(x, reify(Var(x)))
      Σ(e2, ρ2, σ, RebuildLetrec(x, v, ρ1, k))

    // Always rebuild the let.
    case Σ(v, ρ, σ, LetrecCont(x, e2, ρ1, k)) if v.isValue =>
      // Extend the environment with x.
      lazy val ρ2: Env = ρ1.addrec(x, v)
      Σ(e2, ρ2, σ, RebuildLetrec(x, v, ρ1, k))

    // OPTIMIZATION
    // "Split" rules for `let`. Push the residualization of `let` into the context.
    // This has the effect of hoisting the `let` outward, but also allowing
    // evaluation under the `let`.
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, Call(fun, ρ2, k))) if v.isValue && ! (fv(fun) contains x) =>
      Σ(v, ρ, σ, Call(fun, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, EvalArg(arg, ρ2, k))) if v.isValue && ! (fv(arg) contains x) =>
      Σ(v, ρ, σ, EvalArg(arg, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, EvalAlts(alts, ρ2, k))) if v.isValue && ! (fv(Case(Num(0), alts)) contains x) =>
      Σ(v, ρ, σ, EvalAlts(alts, ρ2, RebuildLet(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, OpRight(op, e2, ρ2, k))) if v.isValue && ! (fv(e2) contains x) =>
      Σ(v, ρ, σ, OpRight(op, e2, ρ2, RebuildLet(x, e1, ρ1, k)))

    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, Call(fun, ρ2, k))) if v.isValue && ! (fv(fun) contains x) =>
      Σ(v, ρ, σ, Call(fun, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, EvalArg(arg, ρ2, k))) if v.isValue && ! (fv(arg) contains x) =>
      Σ(v, ρ, σ, EvalArg(arg, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, EvalAlts(alts, ρ2, k))) if v.isValue && ! (fv(Case(Num(0), alts)) contains x) =>
      Σ(v, ρ, σ, EvalAlts(alts, ρ2, RebuildLetrec(x, e1, ρ1, k)))
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, OpRight(op, e2, ρ2, k))) if v.isValue && ! (fv(e2) contains x) =>
      Σ(v, ρ, σ, OpRight(op, e2, ρ2, RebuildLetrec(x, e1, ρ1, k)))


    // collapse redundant lets .. do this even if the focus is not a value!
    // k (let x = e2 in let x = e1 in v)
    // ->
    // k (let x = e1 in v)
    // case Σ(v, ρ, σ, RebuildLet(x1, e1, ρ1, RebuildLet(x2, e2, ρ2, k))) if x1 == x2 && costZero(e1) =>
    //   Σ(v, ρ, σ, RebuildLet(x1, e1, ρ2, k))

    // For other cases, just reify the let _if needed_.
    // In particular, don't generate let x = x in e and don't generate let x = e1 in e2 if x is not free in e2
    // These are harmless except the first prevents use from easily copying and pasting the output into Haskell
    // (because Haskell's let is really letrec and let x = x is a black hole),
    // and the latter makes termination detection more difficult.
    case Σ(v, ρ, σ, RebuildLet(x, Let(y, e1, e2), ρ1, k)) if v.isValue =>
      Σ(v, ρ, σ, RebuildLet(x, e2, ρ1, RebuildLet(y, e1, ρ1, k)))

    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, k)) if v.isValue && (fv(v) contains x) && unreify(e1) != Var(x) =>
      Σ(reify(Let(x, e1, v)), ρ1, σ, k)
    case Σ(v, ρ, σ, RebuildLet(x, e1, ρ1, k)) if v.isValue =>
      // don't reify the let if we don't have to.
      Σ(v, ρ1, σ, k)

    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, k)) if v.isValue && (fv(v) contains x) =>
      Σ(reify(Letrec(x, e1, v)), ρ1, σ, k)
    case Σ(v, ρ, σ, RebuildLetrec(x, e1, ρ1, k)) if v.isValue =>
      // don't reify the letrec if we don't have to.
      Σ(v, ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Case.
    ////////////////////////////////////////////////////////////////
    case Σ(Case(e1, alts), ρ, σ, k) =>
      Σ(e1, ρ, σ, EvalAlts(alts, ρ, k))

    // Quasi-splitting... still need to push the cont down into the alts.
    // To make true splitting. Need to add a residualize continuation
    // (case x of 1 -> x)+2
    // Σ(<x>,Map(),EvalCase(List((\1 -> x)),Map(),OpRight(+,2,Map(),Done)))
    // Rather than residualize the whole case, do each alt with the same continuation,
    // then replace k with Done. (or push upto a certain depth or push until free variable capture?)
    // this is what supercompilation by evaluation does.

    // This is the rule where we have options.
    // We want to try all the alts (in order, to be like Haskell if needed).
    // Pushing the stack into each alt.
    // But we add a barrier (optionally).
    // If more than one alt succeeds, we use the barrier to merge the states.
    // Typically the barrier is just after the case expression... it's Barrier(k) itself.
    // But it could be pushed arbitarily far into k resulting in code explosion as we duplicate
    // the continuation after the case expression.

    // Reify Ctors correctly. Otherwise EvalAlts won't rebuild the case.
    // case Σ(v @ Ctor(n, es), ρ, σ, k) if v.isValue && es.exists { case Residual(_) => true; case _ => false } =>
    //   Σ(reify(Ctor(n, es)), ρ, σ, k)

    // We have two cases. If the scrutinee is a residual, we rebuild the case expression.
    // Otherwise, we evaluate the alts, one of which should match since we have a value.
    // We have to be careful to split here because EvalAlts will not work correctly
    // if given a Residual. FIXME: make it more robust to this. Should really combine
    // EvalAlts and RebuildCase.
    case Σ(Residual(e), ρ, σ, EvalAlts(alts, ρ1, k)) =>
      Σ(reify(e), ρ1, σ, RebuildCase(alts, Nil, ρ1, None, k))

// TODO: push the scrutinee into the alt. If the pattern is a Cons, then we know
// the scrutinee is a Cons. So:
//   case ys of Nil -> e1 | Cons x xs -> e2
//   ==>
//   case [[ys]] of Nil -> let ys = Nil in e1
//                | Cons x xs -> let ys = Cons x xs in e2
    case Σ(v, ρ, σ, EvalAlts(Alt(p, e)::alts, ρ1, k)) if v.isValue =>
      matchPat(v, p, ρ1) match {
        case Some(ρ2) =>
          // Match was successful, evaluate the body of the alt.
          // FIXME: need to restore the ρ in k.
          Σ(e, ρ2, σ, k)
        case None =>
          // Match failed, go to the next alt with the same scrutinee.
          Σ(v, ρ1, σ, EvalAlts(alts, ρ1, k))
      }
    // NOTE: there is no case for EvalAlts(Nil, k) -- it should just fail!

    case Σ(v, ρ, σ, RebuildCase(Alt(p, e)::alts, altsPrime, ρ1, σOpt1, k)) if v.isValue =>
      println("matching " + v + " vs " + p)
      matchPat(v, p, ρ1) match {
        case Some(ρ2) =>
          println("  --> " + ρ2)
          // Match was successful, evaluate the body of the alt.
          // FIXME: need to restore the ρ in k.
          Σ(e, ρ1, σ, RebuildAlt(v, p, alts, altsPrime, ρ1, k))
        case None =>
          println("  --> failed")
          // Match failed, go to the next alt with the same scrutinee.
          Σ(e, ρ1, σ, RebuildCase(alts, altsPrime, ρ1, Some(σOpt1.map(mergeStores(σ, _)).getOrElse(σ)), k))
      }

    case Σ(v, ρ, σ, RebuildCase(Nil, altsPrime, ρ1, σOpt1, k)) if v.isValue =>
      Σ(reify(Case(v, altsPrime.reverse)), ρ1, σOpt1.getOrElse(σ), k)

    case Σ(v, ρ, σ, RebuildAlt(scrutinee, p, alts, altsPrime, ρ1, k)) if v.isValue =>
      Σ(scrutinee, ρ1, σ, RebuildCase(alts, Alt(p, v)::altsPrime, ρ1, Some(σ), k))

      // TODO: a Barrier can be inserted arbitarily deep into k.
      // If immediately before k, we simulate partial evaluation
      // If immediately before the Done at the very bottom of k, we
      // simulate supercompilation.
      // Barriers merge different non-failing continuations.
      // FIXME: confusion between Barrier and Try. If we have Try do we need Barrier?
      // Both are just there to run try all the continuations and then merge the
      // non failing results. I think we still need the barrier to know
      // when to merge the results to get the residual program.

      // Need a new continuation that merges the different alts and rebuilds.
      // Need to record the pattern matching test too so we can recreate the alt.
      // This is getting complicated!!!
      // Better would be to just have some sort of Try and Catch continuations.
      // Try evaluates all possibilities to values.
      // Need to record the pattern match if definitely matches.
      // If _might_ match, need to residualize the matching.
      // Catch takes the results of all the Tries and merges them.
      // Need to handle state too when we extend to CESK.
      // Maybe we should drop the patterns in lambdas as unnecessarily complex,
      // but then again we get residualized lambdas too if we leave it.

      // case Σ(v, ρ, MergeAlts(v1, alts, k) => Σ(Residual(Case(v1, alts), ρ, k)
      // val b = MergeAlts(v, Nil, k)

    ////////////////////////////////////////////////////////////////
    // Unary operators.
    ////////////////////////////////////////////////////////////////

    // Desugar !e into (case e of True -> False | False -> True)
    case Σ(Not(e), ρ, σ, k) =>
      Σ(Case(e, Alt(PCtor("True", Nil), Ctor("False", Nil))::
                Alt(PCtor("False", Nil), Ctor("True", Nil))::Nil), ρ, σ, k)

    // Desugar -e into (0-e)
    case Σ(Neg(e), ρ, σ, k) =>
      Σ(Sub(Num(0), e), ρ, σ, k)

    ////////////////////////////////////////////////////////////////
    // Binary operators.
    ////////////////////////////////////////////////////////////////

    // Just desugar && and || into a case (implementing an if).
    case Σ(Bin(OpAnd, e1, e2), ρ, σ, k) =>
      Σ(Case(e1, Alt(PCtor("True", Nil), e2)::
                 Alt(PCtor("False", Nil), Ctor("False", Nil))::Nil), ρ, σ, k)

    case Σ(Bin(OpOr, e1, e2), ρ, σ, k) =>
      Σ(Case(e1, Alt(PCtor("False", Nil), e2)::
                 Alt(PCtor("True", Nil), Ctor("True", Nil))::Nil), ρ, σ, k)

    // For other binary operations, evaluate the first argument,
    // with a continuation that evaluates the second argument.
    case Σ(Bin(op, e1, e2), ρ, σ, k) =>
      Σ(e1, ρ, σ, OpRight(op, e2, ρ, k))

    // If we have a value and we need to evaluate the second argument
    // of a binary operator, switch the focus to the second argument
    // with a continuation that performs the operation.
    case Σ(v, ρ, σ, OpRight(op, e2, ρ1, k)) if v.isValue =>
      Σ(e2, ρ1, σ, EvalOp(op, v, ρ1, k))

    case Σ(v2, ρ, σ, EvalOp(op, v1, ρ1, k)) if v2.isValue =>
      (op, v1, v2) match {
        // Perform some simple algebraic simplifications
        case (OpAdd, Num(0), v) =>
          Σ(v, ρ1, σ, k)
        case (OpAdd, v, Num(0)) =>
          Σ(v, ρ1, σ, k)
        case (OpSub, v, Num(0)) =>
          Σ(v, ρ1, σ, k)
        case (OpMul, Num(1), v) =>
          Σ(v, ρ1, σ, k)
        case (OpMul, v, Num(1)) =>
          Σ(v, ρ1, σ, k)
        case (OpDiv, v, Num(1)) =>
          Σ(v, ρ1, σ, k)

        case (OpAdd, Num(n1), Num(n2)) => Σ(Num(n1+n2), ρ1, σ, k)
        case (OpSub, Num(n1), Num(n2)) => Σ(Num(n1-n2), ρ1, σ, k)
        case (OpMul, Num(n1), Num(n2)) => Σ(Num(n1*n2), ρ1, σ, k)
        case (OpDiv, Num(n1), Num(0)) => Σ(v2, ρ, σ, Fail(s"div by 0"))
        case (OpMod, Num(n1), Num(0)) => Σ(v2, ρ, σ, Fail(s"mod by 0"))
        case (OpDiv, Num(n1), Num(n2)) => Σ(Num(n1/n2), ρ1, σ, k)
        case (OpMod, Num(n1), Num(n2)) => Σ(Num(n1%n2), ρ1, σ, k)

        case (OpLt, Num(n1), Num(n2)) if n1 < n2 => Σ(Ctor("True", Nil), ρ1, σ, k)
        case (OpLe, Num(n1), Num(n2)) if n1 <= n2 => Σ(Ctor("True", Nil), ρ1, σ, k)
        case (OpGe, Num(n1), Num(n2)) if n1 >= n2 => Σ(Ctor("True", Nil), ρ1, σ, k)
        case (OpGt, Num(n1), Num(n2)) if n1 > n2 => Σ(Ctor("True", Nil), ρ1, σ, k)
        case (OpLt, Num(n1), Num(n2)) => Σ(Ctor("False", Nil), ρ1, σ, k)
        case (OpLe, Num(n1), Num(n2)) => Σ(Ctor("False", Nil), ρ1, σ, k)
        case (OpGe, Num(n1), Num(n2)) => Σ(Ctor("False", Nil), ρ1, σ, k)
        case (OpGt, Num(n1), Num(n2)) => Σ(Ctor("False", Nil), ρ1, σ, k)

        // EXTENSION
        // FIXME: sharing! The let rules seem broken.
        // We want to evaluate under a lambda, but this seems to fail.
        // case (op, Residual(e1), Residual(e2)) if ! e1.isInstanceOf[Var] && ! e2.isInstanceOf[Var] =>
        //   val x1 = FreshVar()
        //   val x2 = FreshVar()
        //   Σ(reify(Let(x1, e1, Let(x2, e2, Bin(op, Var(x1), Var(x2))))), ρ1, k)
        // case (op, v1, Residual(e2)) if ! e2.isInstanceOf[Var] =>
        //   val x2 = FreshVar()
        //   Σ(reify(Let(x2, e2, Bin(op, v1, Var(x2)))), ρ1, k)
        // case (op, Residual(e1), v2) if ! e1.isInstanceOf[Var] =>
        //   val x1 = FreshVar()
        //   Σ(reify(Let(x1, e1, Bin(op, Var(x1), v2))), ρ1, k)

        case (op, v1 @ Residual(e1), v2 @ Residual(e2)) =>
          Σ(reify(Bin(op, v1, v2)), ρ1, σ, k)
        case (op, v1, v2 @ Residual(e2)) =>
          Σ(reify(Bin(op, v1, v2)), ρ1, σ, k)
        case (op, v1 @ Residual(e1), v2) =>
          Σ(reify(Bin(op, v1, v2)), ρ1, σ, k)

        // Equality operators should not work on residuals.
        // So match after the above.
        case (OpEq, v1, v2) if v1 == v2 => Σ(Ctor("True", Nil), ρ1, σ, k)
        case (OpNe, v1, v2) if v1 != v2 => Σ(Ctor("True", Nil), ρ1, σ, k)
        case (OpEq, v1, v2) => Σ(Ctor("False", Nil), ρ1, σ, k)
        case (OpNe, v1, v2) => Σ(Ctor("False", Nil), ρ1, σ, k)

        // Failure
        case _ =>
          Σ(reify(Bin(op, v1, v2)), ρ1, σ, Fail(s"cannot apply operator $op"))
      }

    ////////////////////////////////////////////////////////////////
    // Constructors. TODO: generalize to App.
    ////////////////////////////////////////////////////////////////

    case Σ(Ctor(n, e::es), ρ, σ, k) if ! (e::es).forall(_.isValue) =>
      Σ(e, ρ, σ, EvalCtorArgs(n, es, Nil, ρ, k))

    case Σ(v, ρ, σ, EvalCtorArgs(n, e::es, vs, ρ1, k)) if v.isValue =>
      Σ(e, ρ1, σ, EvalCtorArgs(n, es, v::vs, ρ, k))

    case Σ(v, _, σ, EvalCtorArgs(n, Nil, vs, ρ, k)) if v.isValue =>
      Σ(Ctor(n, (v::vs).reverse), ρ, σ, k)

    // ...
    //
    // OK, so we have a few choices to make. We have a choice about how to split.
    // TODO: implement the Barrier continuation to merge all the alts back into a Case
    // this means Barrier should have the scrutinee as a parameter.
    //
    // Then, we need to add a history and termination detection and generalization
    // We should support naive termination detection, arriving at basic PE
    // Then HE termination detection to support supercompilation.
    //
    // I am not sure how generalization should work. Basically it's introducing new lets
    // to abstract.
    // Distillation is another issue.
    // But these are orthogonal to the core idea of evaluation extended with residualization.
    //
    // So the paper structure is:
    // 1. evaluation
    // 2. partial evaluation (without termination) [extend with residualization]
    // 3. extending with proper splitting
    // 4. extend with naive termination detection and memoization
    // 5. extend with full generalization based on HE
    // 6. extend with full distillation
    // 7. extend with state: CESK machine
    // 8. proofs
    //    - residual evaluates to the same value (and state) as the original program
    //    - performs fewer steps than the original program
    //      - diverges exactly when the original program diverges
    //    - algorithm to compute residual terminates


    ////////////////////////////////////////////////////////////////
    // App and lambda.
    ////////////////////////////////////////////////////////////////

    case Σ(App(fun, arg), ρ, σ, k) =>
      Σ(fun, ρ, σ, EvalArg(arg, ρ, k))

    case Σ(fun, ρ, σ, EvalArg(arg, ρ1, k)) =>
      Σ(arg, ρ1, σ, Call(fun, ρ, k))

    // Eliminate sharing of the argument by building a let for the argument.
    // CBV only
    case Σ(arg, ρ, σ, Call(Lam(x, e), ρ1, k)) if arg.isValue && ! costZero(arg) =>
      Σ(e, ρ1.add(x, reify(Var(x)), ρ), σ, RebuildLet(x, arg, ρ, k))

    case Σ(arg, ρ, σ, Call(Lam(x, e), ρ1, k)) if arg.isValue && (fv(e) contains x) =>
      Σ(e, ρ1.add(x, arg, ρ), σ, RebuildLet(x, arg, ρ, k))

    case Σ(arg, ρ, σ, Call(Lam(x, e), ρ1, k)) if arg.isValue =>
      Σ(e, ρ1.add(x, arg, ρ), σ, k)

    case Σ(arg, ρ, σ, Call(fun, ρ1, k)) if arg.isValue =>
      Σ(reify(App(fun, arg)), ρ1, σ, k)

    ////////////////////////////////////////////////////////////////
    // Infrastructure cases.
    ////////////////////////////////////////////////////////////////

    case s @ Σ(_, _, σ, Done) => s
    case s @ Σ(_, _, σ, Fail(_)) => s
    case s @ Σ(e, ρ, σ, k) =>
      Σ(e, ρ, σ, Fail(s"no step defined for $s"))
  }

  // In SC / PE, we get stuck when focus is a Var!
  // Add continuations for Bin and for Case, etc.

  // PE builds the residual directly.
  // In PE, when we get "stuck", we recurse on subexpressions.
  // Can we *add* residualization to the continuation...
  // e.g., when doing x+2
  // we get to the configuration: (x, [], OpRight(+, 2, k))
  // then we go to the configuration: (2, [], EvalOp(+, x, k))
  // then we want to eval x+2, but we can't so we make a "value" for x+2
  // to avoid repeating we do Residual(x+2).
  // We do this rather than splitting?

  def strongReify(ρ: Env): Env = ρ match {
    case MapEnv(m) => MapEnv(m.map {
      case (x, Closure(e, ρ)) => (x, Closure(strongReify(e), strongReify(ρ)))
    })
    case SelfEnv => SelfEnv
  }

  def strongReify(s: St): St = s match {
    case Σ(focus, ρ, σ, k) =>
      val vars = fv(focus)
      // val vars = focus match { case Var(x) => Set(x) ; case _ => Set() }
      val k1 = vars.toList.foldLeft(k) {
        case (k, x) =>
          ρ.get(x) match {
            case Some(Closure(v, ρ)) =>
              RebuildLet(x, unreify(v), ρ, k)
            case None =>
              k
          }
      }
      Σ(strongReify(focus), strongReify(ρ), σ, k1)
  }

  // To convert to a term just reify the focus and run the machine to termination.
  def toTerm(s: St): Option[Exp] = {
    println("converting to term " + s)
    s match {
      case Σ(focus, ρ, σ, Done) =>
        val e = unreify(focus)
        println("--> " + e)
        Some(e)
      case Σ(focus, ρ, σ, Fail(_)) =>
        None
      case s =>
        toTerm(step(strongReify(s)))
    }
  }

  // Homeomorphic embedding code
  implicit class ExpHE(e1: Exp) {
    def <<|(e2: Exp): Boolean = he(e1, e2)

    def he(e1: Exp, e2: Exp) = diving(e1, e2) || coupling(e1, e2)

    def diving(t1: Exp, t2: Exp): Boolean = t2 match {
      case App(e1, e2) => he(t1, e1) || he(t1, e2)
      case Bin(_, e1, e2) => he(t1, e1) || he(t1, e2)
      case Neg(e) => he(t1, e)
      case Not(e) => he(t1, e)
      case Ctor(k, es) => es.exists(he(t1, _))
      case Let(x, e1, e2) => he(t1, e1) || he(t1, e2)
      case Letrec(x, e1, e2) => he(t1, e1) || he(t1, e2)
      case Case(e, alts) => he(t1, e) || alts.exists { case Alt(p, e) => he(t1, e) }
      case Lam(x, e) => he(t1, e)
      case Var(_) => false
      case Num(_) => false
      case Residual(e) => he(t1, e)
    }

    def coupling(t1: Exp, t2: Exp): Boolean = (t1, t2) match {
      case (Var(_), Var(_)) => true
      case (App(f1, a1), App(f2, a2)) => he(f1, f2) && he(a1, a2)
      case (Bin(op1, f1, a1), Bin(op2, f2, a2)) => op1 == op2 && he(f1, f2) && he(a1, a2)
      case (Not(a1), Not(a2)) => he(a1, a2)
      case (Neg(a1), Neg(a2)) => he(a1, a2)
      case (Ctor(k1, es1), Ctor(k2, es2)) => k1 == k2 && es1.length == es2.length && (es1 zip es2).forall { case (e1, e2) => he(e1, e2) }
      case (Num(k1), Num(k2)) => k1 == k2
      case (Lam(x1, e1), Lam(x2, e2)) => he(e1, e2)
      case (Let(x1, e1, f1), Let(x2, e2, f2)) => he(e1, e2) && he(f1, f2)
      case (Letrec(x1, e1, f1), Letrec(x2, e2, f2)) => he(e1, e2) && he(f1, f2)
      case (Case(e1, alts1), Case(e2, alts2)) =>
        he(e1, e2) && alts1.length == alts2.length && (alts1 zip alts2).forall {
          case (Alt(p1, e1), Alt(p2, e2)) => he(e1, e2)
        }
      case (Residual(e1), Residual(e2)) => coupling(e1, e2)
      case (e1, Residual(e2)) => coupling(e1, e2)
      case (Residual(e1), e2) => coupling(e1, e2)
      case _ => false
    }
  }

  implicit class ContHE(k1: Cont) {
    def <<|(k2: Cont): Boolean = coupling(k1, k2)

    def coupling(k1: Cont, k2: Cont) = (k1, k2) match {
      case (Done, Done) => true
      case (Fail(_), Fail(_)) => true
      case (EvalArg(e1, ρ1, k1), EvalArg(e2, ρ2, k2)) => e1 <<| e2 && k1 <<| k2
      case (Call(e1, ρ1, k1), Call(e2, ρ2, k2)) => e1 <<| e2 && k1 <<| k2
      case (OpRight(op1, e1, ρ1, k1), OpRight(op2, e2, ρ2, k2)) if op1 == op2 => e1 <<| e2 && k1 <<| k2
      case (EvalOp(op1, e1, ρ1, k1), EvalOp(op2, e2, ρ2, k2)) if op1 == op2 => e1 <<| e2 && k1 <<| k2
      case (EvalCtorArgs(n1, es1, fs1, ρ1, k1), EvalCtorArgs(n2, es2, fs2, ρ2, k2)) if n1 == n2 && es1.length == es2.length =>
        (es1 zip es2).forall { case (e1, e2) => e1 <<| e2 } && k1 <<| k2
      case (LetCont(x1, e1, ρ1, k1), LetCont(x2, e2, ρ2, k2)) if x1 == x2 => e1 <<| e2 && k1 <<| k2
      case (LetrecCont(x1, e1, ρ1, k1), LetrecCont(x2, e2, ρ2, k2)) if x1 == x2 => e1 <<| e2 && k1 <<| k2
      case (RebuildLet(x1, e1, ρ1, k1), RebuildLet(x2, e2, ρ2, k2)) if x1 == x2 => e1 <<| e2 && k1 <<| k2
      case (RebuildLetrec(x1, e1, ρ1, k1), RebuildLetrec(x2, e2, ρ2, k2)) if x1 == x2 => e1 <<| e2 && k1 <<| k2
      case (EvalCase(alts1, ρ1, k1), EvalCase(alts2, ρ2, k2)) if alts1.length == alts2.length =>
        (alts1 zip alts2).forall { case (Alt(_, e1), Alt(_, e2)) => e1 <<| e2 } && k1 <<| k2
      case (EvalAlts(alts1, ρ1, k1), EvalAlts(alts2, ρ2, k2)) if alts1.length == alts2.length =>
        (alts1 zip alts2).forall { case (Alt(_, e1), Alt(_, e2)) => e1 <<| e2 } && k1 <<| k2
      case (RebuildCase(alts1, _, ρ1, _, k1), RebuildCase(alts2, _, ρ2, _, k2)) if alts1.length == alts2.length =>
        (alts1 zip alts2).forall { case (Alt(_, e1), Alt(_, e2)) => e1 <<| e2 } && k1 <<| k2
      case (RebuildAlt(e1, _, alts1, _, ρ1, k1), RebuildAlt(e2, _, alts2, _, ρ2, k2)) if alts1.length == alts2.length =>
        (alts1 zip alts2).forall { case (Alt(_, e1), Alt(_, e2)) => e1 <<| e2 } && e1 <<| e2 && k1 <<| k2
      case _ => false
    }
  }

  implicit class StHE(s1: St) {
    def size(e: Exp): Int = e match {
      case Num(_) => 1
      case Ctor(_, es) => es.map(size(_)).sum + 1
      case App(e1, e2) => size(e1) + size(e2) + 1
      case Bin(_, e1, e2) => size(e1) + size(e2) + 1
      case Not(e) => size(e) + 1
      case Neg(e) => size(e) + 1
      case Var(_) => 1
      case Lam(_, e) => size(e) + 1
      case Let(x, e1, e2) => size(e1) + size(e2)
      case Letrec(x, e1, e2) => size(e1) + size(e2)
      case Case(e, alts) => size(e) + alts.map { case Alt(p, e) => size(e) }.sum + 1
      case Residual(e) => size(e)
    }

    def size(k: Cont, e: Exp): Int = size(k, size(e))

    def size(k: Cont, n: Int): Int = {
      k match {
        case Done => n
        case Fail(_) => n
        case EvalArg(e1, ρ1, k1) => size(k1, size(e1) + n + 1)
        case Call(e1, ρ1, k1) => size(k1, size(e1) + n + 1)
        case OpRight(op1, e1, ρ1, k1) => size(k1, n + size(e1) + 1)
        case EvalOp(op1, e1, ρ1, k1) => size(k1, size(e1) + n + 1)
        case EvalCtorArgs(n1, es1, fs1, ρ1, k1) => size(k1, es1.map(size(_)).sum + n + 1)
        case LetCont(x1, e1, ρ1, k1) => size(k1, n + size(e1))
        case LetrecCont(x1, e1, ρ1, k1) => size(k1, n + size(e1))
        case RebuildLet(x1, e1, ρ1, k1) => size(k1, n + size(e1))
        case RebuildLetrec(x1, e1, ρ1, k1) => size(k1, n + size(e1))
        case EvalCase(alts1, ρ1, k1) => size(k1, n + alts1.map { case Alt(p, e) => size(e) }.sum + 1)
        case EvalAlts(alts1, ρ1, k1) => size(k1, n + alts1.map { case Alt(p, e) => size(e) }.sum + 1)
        case RebuildCase(alts1, _, ρ1, _, k1) => size(k1, n + alts1.map { case Alt(p, e) => size(e) }.sum + 1)
        case RebuildAlt(e1, _, alts1, _, ρ1, k1) => size(k1, n + size(e1) + alts1.map { case Alt(p, e) => size(e) }.sum)
      }
    }

    def <<|(s2: St): Boolean = (s1, s2) match {
      case (Σ(e1, ρ1, σ1, k1), Σ(e2, ρ2, σ2, k2)) =>
        ! e1.isInstanceOf[Lam] &&
        ! e2.isInstanceOf[Lam] &&
        e1 == e2 &&
        k1 <<| k2 &&
        size(k1, e1) < size(k2, e2)
    }
  }

  // termination:
  // a precondition of nintermination is that values grow.
  // but this is difficult to implement here because we have numbers (which "change' not grow")
  //
  // Homeomorphic embedding says a previous state is a subsequence of the new state.
  // HE works well with terms.
  // tagbags are an approximation: a well-quasi order
  //
  // states are more complicated.
  // simple test.... if we run ahead 1000 steps, do we terminate?
  // if yes, ok.
  // if not, then, we can either just run ahead 1000 steps or we can generalize the two states
  // in the history
  // So, don't bother with the HE or anything like that.
  // This may actually work very well in practice because we won't PE code forever

  implicit class Folder(s1: St) {
    // Is s2 a rename of s1?
    // If so, we generate a new function and call it.
    def tryFold(s2: St): Option[St] = {
      def unify(s1: St, s2: St): Option[List[(Name, Exp)]] = {
        if (s1 == s2) Some(Nil)
        else None
      }

      unify(s1, s2) map {
        case subst =>
          s2 match {
            case Σ(e, ρ, σ, k) =>
              val f = FreshVar()
              val app = subst.foldLeft(Var(f): Exp) {
                case (e, (x, v)) => App(e, v)
              }
              val lam = subst.foldRight(e: Exp) {
                case ((x,v), lam) => Lam(x, lam)
              }
              // The rebuild should float out to the top
              Σ(Residual(app), ρ, σ, RebuildLetrec(f, lam, ρ, k))
          }
      }
    }
  }

  // Continuation generalization.
  // We fold two states that have the same focus and different continuations.
  // (e, k1) fold (e, k2)
  // where k1 = k1' ++ k
  //       k2 = k2' ++ k
  // we generalize k1' and k2' to k', getting k' ++ k
  // then we restart in (e, k' ++ k)

  def generalize(k1: Cont, k2: Cont): Cont = {
    if (k1 eq k2) return k1
    if (k1 == k2) return k1
    (k1, k2) match {
      case (k1, k2) => k1
    }
  }

  // Termination works as follows.
  // First: folding. If a new state (possibly ignoring some of the continuation)
  // is a renaming of a previous
  // state, then we fold. We introduce a function and generate a call to the function.
  //
  // generate new name f, rebuild let should get pushed out to the top.
  // or do we need a "global environment"
  // fold (e, p, s, k) = ([[f ()]], p, s, RebuildLet(f, [[\_ -> e]], k))

  def eval(e: Exp, maxSteps: Int): Exp = {
    var s = inject(e)

    val hist: ListBuffer[St] = ListBuffer()
    hist += s

    var t = maxSteps

    while (true) {
      t -= 1
      println(s)

      s match {
        // stop when we have a value with the empty continuation.
        case Σ(v, _, σ, Done) if v.isValue =>
          return v

        case Σ(v, _, σ, Fail(s)) if v.isValue =>
          return Lam("error", v)

        case s0 @ Σ(e, ρ, σ, k) if t == 0 =>
          val s1 = step(s0)
          println(s"aborting...")
          return Lam("nontermination", e)

        case s0 @ Σ(focus, ρ, σ, k) =>
          val s1 = step(s0)

          s1 match {
            case Σ(focus1 @ Var(x), ρ1, σ, k1) =>
              s = hist.foldRight(s1) {
                case (prev, s_) if s1 == s_ => prev.tryFold(s1) match {
                  case Some(s3) =>
                    println(s"FOLD: $prev ==| $s1 ==> $s3")
                    s3
                  case None =>
                    if (prev == s1 || prev <<| s1) {
                      println(s"WHISTLE: $prev <<| $s1")
                      strongReify(s1)
                    }
                    else {
                      // keep going
                      s1
                    }
                }
                case (prev, s2) =>
                  s2
              }

              hist += s
            case s1 =>
              s = s1
          }
      }
    }

    throw new RuntimeException("unreachable")
  }
}

// TODO: to perform reification, need to incorporate the environment better.
// When we add something to the environment, we should add a rebuild continuation
// that basically adds a let if needed. We should have a let binding for each
// free variable in the residualized focus when we get to the Done continuation.
// But, then need to order the lets to make the environments work out correctly.
