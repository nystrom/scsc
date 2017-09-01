package sc.jsai.sc

// For Kiama to work correctly states cannot be defined as nested classes.
// Define them in a companion object instead.
object Supercompiler {

  import sc.core.sc.Unsplit._

  import notjs.syntax._
  import notjs.abstracted.domains._
  import notjs.abstracted.interpreter.{State ⇒ Σ}

  type State = Σ

  import notjs.abstracted.eval.Eval.eval

  // Partial evaluation of expressions
  object PEval {
    def peval(e: Exp, ρ:Env, σ:Store, ß:Scratchpad): Exp = e match {
      case e @ NumAST(d) ⇒ e
      case e @ BoolAST(b) ⇒ e
      case e @ StrAST(str) ⇒ e
      case e @ UndefAST() ⇒ e
      case e @ NullAST() ⇒ e

      case x:PVar ⇒ toAST(x, σ(ρ(x)))
      case x:Scratch ⇒ toAST(x, ß(x))

      case e @ Binop(op, e1, e2) ⇒
        val bv = eval(e, ρ, σ, ß)
        lazy val enew = Binop(op, peval(e1, ρ, σ, ß), peval(e2, ρ, σ, ß))
        toAST(enew, bv)

      case e @ Unop(op, e1) ⇒
        val bv = eval(e, ρ, σ, ß)
        lazy val enew = Unop(op, peval(e1, ρ, σ, ß))
        toAST(enew, bv)
    }

    def toAST(e: => Exp, bv: BValue): Exp = {
      if (bv.defNum) {
        bv.n match {
          case NConst(d) ⇒ NumAST(d)
          case _ ⇒ e
        }
      }
      else if (bv.defBool) {
        bv.b match {
          case Bool.True ⇒ BoolAST(true)
          case Bool.False ⇒ BoolAST(false)
          case _ ⇒ e
        }
      }
      else if (bv.defStr) {
        bv.str match {
          case SConstNum(str) ⇒ StrAST(str)
          case SConstSpl(str) ⇒ StrAST(str)
          case SConstNotSplNorNum(str) ⇒ StrAST(str)
          case _ ⇒ e
        }
      }
      else if (bv == Null.BV) {
        NullAST()
      }
      else if (bv == Undef.BV) {
        UndefAST()
      }
      else {
        e
      }
    }
  }

  import PEval._

  object SplitHelper {
    // Logical negation of a BV, but we're trying to compute
    // the preimage of the bv, so even if we have a boolean,
    // it could have been converted from a non-boolean, so
    // we can't just return a boolean.
    def preNot(bv: BValue): BValue = {
      if (bv.b == Bool.True) {
        Bool.FalseBV
      }
      else if (bv.b == Bool.False) {
        Bool.TrueBV
      }
      else {
        BValue.⊥
      }
    }

    // Preimage of !=. Return an abstract value
    // representing all values not === to bv.
    def preNotEqual(bv: BValue) = {
      if (bv.defBool) {
        bv.logicnot
      }
      else {
        BValue.⊥
      }
    }

    implicit class MeetNum(n1: Num) {
      def ⊓( n2:Num ): Num = n1
    }
    implicit class MeetBool(b1: Bool) {
      def ⊓( b2:Bool ): Bool =
        (b1, b2) match {
          case (x, y) if x == y ⇒ b1
          case (BTop, x) ⇒ x
          case (x, BTop) ⇒ x
          case (BBot, _) | (_, BBot) | (BTrue, BFalse) | (BFalse, BTrue) ⇒ BBot
          case _ ⇒ sys.error("suppress false compiler warning")
        }

    }
    implicit class MeetStr(s1: Str) {
      def ⊓( s2:Str ): Str =
        (s1, s2) match {
          case (x, y) if x == y ⇒ s1
          case (STop, x) ⇒ x
          case (x, STop) ⇒ x
          case (SBot, _) | (_, SBot) | (_, _) ⇒ SBot
          case _ ⇒ sys.error("suppress false compiler warning")
        }

    }
    import notjs.abstracted.domains.AddressSpace.Addresses

    implicit class MeetAddresses(as1: Addresses) {
      def ⊓( as2:Addresses ): Addresses = as1 intersect as2
    }
    implicit class MeetNull(b1: Null) {
      def ⊓( b2:Null ): Null =
        (b1, b2) match {
          case (x, y) if x == y ⇒ b1
          case (MaybeNull, x) ⇒ x
          case (x, MaybeNull) ⇒ x
          case (NotNull, _) | (_, NotNull) ⇒ NotNull
          case _ ⇒ sys.error("suppress false compiler warning")
        }
    }
    implicit class MeetUndef(b1: Undef) {
      def ⊓( b2:Undef ): Undef =
        (b1, b2) match {
          case (x, y) if x == y ⇒ b1
          case (MaybeUndef, x) ⇒ x
          case (x, MaybeUndef) ⇒ x
          case (NotUndef, _) | (_, NotUndef) ⇒ NotUndef
          case _ ⇒ sys.error("suppress false compiler warning")
        }
    }

    implicit class MeetBV(bv1: BValue) {
      def ⊓( bv2:BValue ): BValue =
        BValue( bv1.n ⊓ bv2.n, bv1.b ⊓ bv2.b, bv1.str ⊓ bv2.str, bv1.as ⊓ bv2.as,
                bv1.nil ⊓ bv2.nil, bv1.undef ⊓ bv2.undef )
    }

    // Simulate predicates on the store
    def simulatePredσ(e:Exp, ρ:Env, σ:Store, ß:Scratchpad, result: BValue): Store = {
      simulatePred(e, ρ, σ, ß, result)._1
    }

    // Simulate predicates on the scratchpad
    def simulatePredß(e:Exp, ρ:Env, σ:Store, ß:Scratchpad, result: BValue): Scratchpad = {
      simulatePred(e, ρ, σ, ß, result)._2
    }

    // Simulate predicates on the store and scratchpad
    // We use the ⊓ operator on values to just add more
    // information to the store, not replace existing
    // information.
    def simulatePred(e:Exp, ρ:Env, σ:Store, ß:Scratchpad, result: BValue): (Store, Scratchpad) = e match {
      case x:Scratch ⇒
        if (ß(x) != ß(x) ⊓ result) println(s"AUGMENTING $x from ${ß(x)} to ${ß(x) ⊓ result}")
        (σ, ß(x) = ß(x) ⊓ result)
      case x:PVar ⇒
        if (σ(ρ(x)) != σ(ρ(x)) ⊓ result) println(s"AUGMENTING $x from ${σ(ρ(x))} to ${σ(ρ(x)) ⊓ result}")
        (σ + (ρ(x) → (σ(ρ(x)) ⊓ result)), ß)
      case Binop(⌜&&⌝, e1, e2) if result.tobool == Bool.True ⇒
        val (σ1, ß1) = simulatePred(e1, ρ, σ, ß, result)
        simulatePred(e2, ρ, σ1, ß1, result)
      case Binop(⌜||⌝, e1, e2) if result.tobool == Bool.False ⇒
        val (σ1, ß1) = simulatePred(e1, ρ, σ, ß, result)
        simulatePred(e2, ρ, σ1, ß1, result)
      case Binop(⌜≡⌝, x:Var, e) if result.tobool == Bool.True ⇒
        val bv = eval(e, ρ, σ, ß)
        simulatePred(x, ρ, σ, ß, bv)
      case Binop(⌜≡⌝, e, x:Var) if result.tobool == Bool.True ⇒
        val bv = eval(e, ρ, σ, ß)
        simulatePred(x, ρ, σ, ß, bv)
      case Binop(⌜≡⌝, x:Var, e) if result.tobool == Bool.False ⇒
        val bv = eval(e, ρ, σ, ß)
        simulatePred(x, ρ, σ, ß, preNotEqual(bv))
      case Binop(⌜≡⌝, e, x:Var) if result.tobool == Bool.False ⇒
        val bv = eval(e, ρ, σ, ß)
        simulatePred(x, ρ, σ, ß, preNotEqual(bv))
      case Unop(⌞¬⌟, e) ⇒
        simulatePred(e, ρ, σ, ß, preNot(result))
      case _ ⇒
        (σ, ß)
    }


    // The AI does the splitting for us with ςnext.
    // We need to reconstruct the split based on
    // the next states so we can rebuild the node
    // in the right order.
    // We assume if ςnext is unique, we don't split.
    def augment(ς: Σ, ςnext: List[Σ]) = (ς, ςnext) match {
      case (ς, Nil) ⇒ None
      case (ς, ς1::Nil) ⇒ None

      case (Σ(StmtT(If(e, s1, s2)), ρ, σ, ß, κs, τ),
            (ς1 @ Σ(StmtT(s1a), ρ1, σ1, ß1, κs1, τ1))::
            (ς2 @ Σ(StmtT(s2a), ρ2, σ2, ß2, κs2, τ2))::
            Nil) if s1 == s1a && s2 == s2a ⇒

            // ς1 is the true branch
            // ς2 is the false branch
            val ς1a = ς1.copy(σ = simulatePredσ(e, ρ1, σ1, ß1, Bool.TrueBV),
                              ß = simulatePredß(e, ρ1, σ1, ß1, Bool.TrueBV))
            val ς2a = ς2.copy(σ = simulatePredσ(e, ρ2, σ2, ß2, Bool.FalseBV),
                              ß = simulatePredß(e, ρ2, σ2, ß2, Bool.FalseBV))

            val ςs = ς1a::ς2a::Nil
            ςs

      case (Σ(StmtT(If(e, s1, s2)), ρ, σ, ß, κs, τ),
            (ς2 @ Σ(StmtT(s2a), ρ2, σ2, ß2, κs2, τ2))::
            (ς1 @ Σ(StmtT(s1a), ρ1, σ1, ß1, κs1, τ1))::
            Nil) if s1 == s1a && s2 == s2a ⇒

            // ς1 is the true branch
            // ς2 is the false branch
            val ς1a = ς1.copy(σ = simulatePredσ(e, ρ1, σ1, ß1, Bool.TrueBV),
                              ß = simulatePredß(e, ρ1, σ1, ß1, Bool.TrueBV))
            val ς2a = ς2.copy(σ = simulatePredσ(e, ρ2, σ2, ß2, Bool.FalseBV),
                              ß = simulatePredß(e, ρ2, σ2, ß2, Bool.FalseBV))

            val ςs = ς1a::ς2a::Nil
            ςs

      case (Σ(StmtT(While(e, s)), ρ, σ, ß, κs, τ),
            (ς1 @ Σ(StmtT(s1a), ρ1, σ1, ß1, κs1, τ1))::
            (ς2 @ Σ(StmtT( _ ), ρ2, σ2, ß2, κs2, τ2))::
            Nil) if s == s1a ⇒

            // ς1 is the loop body branch
            // ς2 is the loop exit branch
            val ς1a = ς1.copy(σ = simulatePredσ(e, ρ1, σ1, ß1, Bool.TrueBV),
                              ß = simulatePredß(e, ρ1, σ1, ß1, Bool.TrueBV))
            val ς2a = ς2.copy(σ = simulatePredσ(e, ρ2, σ2, ß2, Bool.FalseBV),
                              ß = simulatePredß(e, ρ2, σ2, ß2, Bool.FalseBV))

            val ςs = ς1a::ς2a::Nil
            ςs

      case (Σ(StmtT(While(e, s)), ρ, σ, ß, κs, τ),
            (ς2 @ Σ(StmtT( _ ), ρ2, σ2, ß2, κs2, τ2))::
            (ς1 @ Σ(StmtT(s1a), ρ1, σ1, ß1, κs1, τ1))::
            Nil) if s == s1a ⇒

            // ς1 is the loop body branch
            // ς2 is the loop exit branch
            val ς1a = ς1.copy(σ = simulatePredσ(e, ρ1, σ1, ß1, Bool.TrueBV),
                              ß = simulatePredß(e, ρ1, σ1, ß1, Bool.TrueBV))
            val ς2a = ς2.copy(σ = simulatePredσ(e, ρ2, σ2, ß2, Bool.FalseBV),
                              ß = simulatePredß(e, ρ2, σ2, ß2, Bool.FalseBV))

            val ςs = ς1a::ς2a::Nil
            ςs

      // here t is the last statement of the previous loop
      // iteration and we're going to try to go around again
      case (Σ(t, ρ, σ, ß, KStack(WhileK(e, s)::_, _), τ),
            (ς1 @ Σ(StmtT(s1a), ρ1, σ1, ß1, κs1, τ1))::
            (ς2 @ Σ(StmtT( _ ), ρ2, σ2, ß2, κs2, τ2))::
            Nil) if s == s1a ⇒

            // ς1 is the loop body branch
            // ς2 is the loop exit branch
            val ς1a = ς1.copy(σ = simulatePredσ(e, ρ1, σ1, ß1, Bool.TrueBV),
                              ß = simulatePredß(e, ρ1, σ1, ß1, Bool.TrueBV))
            val ς2a = ς2.copy(σ = simulatePredσ(e, ρ2, σ2, ß2, Bool.FalseBV),
                              ß = simulatePredß(e, ρ2, σ2, ß2, Bool.FalseBV))

            val ςs = ς1a::ς2a::Nil
            ςs

      case (Σ(t, ρ, σ, ß, KStack(WhileK(e, s)::_, _), τ),
            (ς2 @ Σ(StmtT( _ ), ρ2, σ2, ß2, κs2, τ2))::
            (ς1 @ Σ(StmtT(s1a), ρ1, σ1, ß1, κs1, τ1))::
            Nil) if s == s1a ⇒

            // ς1 is the loop body branch
            // ς2 is the loop exit branch
            val ς1a = ς1.copy(σ = simulatePredσ(e, ρ1, σ1, ß1, Bool.TrueBV),
                              ß = simulatePredß(e, ρ1, σ1, ß1, Bool.TrueBV))
            val ς2a = ς2.copy(σ = simulatePredσ(e, ρ2, σ2, ß2, Bool.FalseBV),
                              ß = simulatePredß(e, ρ2, σ2, ß2, Bool.FalseBV))

            val ςs = ς1a::ς2a::Nil
            ςs

      case _ ⇒
        ςnext
    }
  }
}

trait Supercompiler {
  import Supercompiler._

  import scala.collection.mutable.ListBuffer
  import scala.collection.immutable.{Seq ⇒ Sequence}

  import sc.core.sc.Unsplit._

  import notjs.abstracted.interpreter.{State ⇒ Σ}
  import notjs.translator.jsast._
  import notjs.abstracted.init._
  import notjs.syntax._
  import notjs.abstracted.domains._
  import notjs.abstracted.traces._
  import TraceHelper._

  object SC extends sc.core.sc.SC[State] {
    def interp = Interpreter
    override val theMetaWhistle = MetaWhistles.DepthWhistle(100) | MetaWhistles.SplitDepthWhistle(20)

    // override the SC algorithm allow step to return multiple
    // states
    override def supercompile(start: State): Option[State] = {
      import notjs.abstracted.interpreter.notJS.Mutable
      import notjs.abstracted.interpreter.PruneScratch
      import notjs.abstracted.interpreter.PruneStoreToo
      import scala.collection.mutable.HashSet

      Mutable.clear
      PruneScratch.clear
      PruneStoreToo.clear
      Mutable.splitStates = false
      Mutable.fullGC = false
      Mutable.lightGC = true
      Mutable.pruneStore = true
      notjs.abstracted.interpreter.Stats.trackStats = true
      notjs.abstracted.interpreter.Stats.exceptions.clear

      type History = List[State]
      var worklist: List[History] = List(List(start))
      var complete: List[History] = List()
      val folded: HashSet[History] = new HashSet()
      var iter = 0

      while (worklist.nonEmpty) {
        val history = worklist.head
        worklist = worklist.tail

        history match {
          case Nil =>
          case ς::h =>
            // println(s"DRIVE ${sc.util.PPAny.ugly(history)}")
            iter += 1
            println(s"DRIVE iter=$iter len=${h.length+1} ws=${worklist.length}")
            notjs.abstracted.interpreter.Stats.report

            interp.fold(ς::h) match {
              case Some(ς1::h1) =>
                // folded with a previous state.
                // there is a state ς2 that is smaller than ς
                // ς1 = ς2 join ς
                // if we've already seen the generalized history,
                // don't add it back to the worklist
                println(s"FOLDED")
                println(s"ς .τ = ${ς.τ}")
                println(s"ς1.τ = ${ς1.τ}")
                // ignore the trace when checking if memoized, otherwise we'll always fail
                // to find it some OmegaCFA are unique
                if (! (folded exists {
                    case Nil => false
                    case ς0::h0 => h0 == h1 && ς0.copy(τ = ς1.τ) == ς1 })) {
                  println(s"FOLDED: ADDING TO WORKLIST")
                  // println(s"FOLDED FROM ${sc.util.PPAny.ugly(ς)}")
                  // println(s"FOLDED TO ${sc.util.PPAny.ugly(ς1)}")
                  folded += (ς1::h1)
                  worklist = (ς1::h1) :: worklist
                }
                else {
                  println(s"FOLDED: COMPLETE")
                  complete = (ς1::h1) :: complete
                }
              case _ =>
                // Note, we don't have a whistle per se
                // because we will always fold if the
                // we reach the same program point twice
                // and the later state embeds the earlier.
                // That is, we make the HE whistle into
                // the fold.
                ς.next.toList match {
                  case Nil =>
                    // stuck or halted
                    println(s"HALT")
                    complete = (ς::h) :: complete
                  case ς1::Nil =>
                    // returned one or more states
                    if (W.mightDiverge(ς))
                      worklist = (ς1::ς::h) :: worklist
                    else
                      worklist = (ς1::h) :: worklist
                  case ςs =>
                    // returned two or more states
                    // try to add information to the state about which
                    // path was taken
                    import SplitHelper._
                    val ςs1 = augment(ς, ςs)
                    if (W.mightDiverge(ς)) {
                      val hs = ςs.map(_::ς::h)
                      worklist = hs ++ worklist
                    }
                    else {
                      val hs = ςs.map(_::h)
                      worklist = hs ++ worklist
                    }
                }
            }
        }
      }

      // complete foreach {
      //   case ς::h =>
      //     println(s"COMPLETE ${sc.util.PPAny.ugly(ς.t)}")
      //     println(s"COMPLETE ${sc.util.PPAny.ugly(ς.σ)}")
      //     println(s"COMPLETE ${sc.util.PPAny.ugly(ς.ß)}")
      //   case _ =>
      // }

      println(s"COMPLETE ${complete.length} histories")

      None
    }


  }


  // We use a trace that has infinite context-sensitivity and
  // infinite heap-sensitivity.

  // Flow-sensitive stack-based infinite-CFA with infinite-sensitive heap
  case class OmegaCFA(pp: Int, next: Int) extends SameTrace[OmegaCFA] {
    def ⊔( other: OmegaCFA ): Option[OmegaCFA] = {
      if (pp == other.pp)
        Some(OmegaCFA(pp, next max other.next))
      else
        None
    }

    // flow-sensitive
    def updateSame( s: Stmt ) =
      OmegaCFA(s.id, Fresh()) //, tr)

    // the program point of the current trace is the caller site
    // push caller site to the call history
    def updateSame( ρ:Env, σ: Store, self: BValue, args:BValue, s:Stmt ) =
      OmegaCFA(s.id, Fresh()) //, pp +: tr)

    def toAddr =
      IntsToBigInt(next::Nil, pp)

    def makeAddr( x:Var ) =
      // Unlike other traces, we just allocate
      // a fresh address.
      IntsToBigInt(next::Nil, x.id)
  }

  import org.bitbucket.inkytonik.kiama.util.Counter
  object Fresh extends Counter {
    def apply() = next()
  }

  object OmegaCFA {
    def apply(): OmegaCFA =
      OmegaCFA(0, 0)//, Sequence[Int]())
  }

  // The relation with AI is as follows.
  // In AI, we memoize states by their trace
  // (the top k of the call stack, for instance).
  // In SC, we record the entire state history and
  // fold to previous states.
  // In both, we split when information is uncertain.
  // In SC, we compute a residual program.
  // In AI, we compute analysis results.

  // In AI we drive until a merge point only, then memoize
  // In SC, we drive until the end of the continuation, merging
  // only when the whistle blows.

  object Interpreter extends sc.core.sc.Interpreter[State] with W {
    private type History = List[State]

    // Step to the next state
    def step(ς: State): Option[State] = None

    // Check if we should stop driving.
    def whistle(h: History): Boolean = theWhistle.blow(h)

    val theWhistle: Whistle = DepthWhistle(50) | (MightDivergeWhistle & TagbagWhistle)
    // val theWhistle: Whistle = DepthWhistle(100) | ((LoopWhistle() | RecursiveCallWhistle()) & HEWhistle())
    // val theWhistle: Whistle = DepthWhistle(100)
    // val theWhistle: Whistle = NoWhistle

    // Fold the last element of the current history with a previous element, truncating
    // the history. The new last element of the history generalizes the old last element
    // and the previous element.
    // FIXME: other SC algorithms aren't restricted to folding with ancestors.
    // They can fold with any previously completed state (for instance in a memo table of bindings).
    def fold(h: History): Option[History] = h match {
      case ς::h if mightDiverge(ς) ⇒
        // This version of fold replaces a simple loop in the history with the root
        // of the history.
        val sameTerm = h.view.zipWithIndex.filter { case (prev, i) => prev.t == ς.t }

        sameTerm foreach {
          case (prev, i) =>
            generalize(ς, prev) match {
              case Some(ς1) =>
                println(s"DROPPING ${i+1} from history")
                val h1 = ς1 :: h.drop(i+1)
                assert(h1.length < (ς::h).length)
                return Some(h1)
              case None =>
            }
        }
        None
      case _ => None
    }


    // Construct a new state from the current history.
    // This is not allowed to fail!
    // Since states in the history are all equivalent, we can just reutrn
    // any state in the history, but clearly the first (newest) state is best.
    // However, the point is to be able to produce a residual term from
    // the state, so we actually try to convert the history to a Re.
    def rebuild(h: History): State = h match {
      case ς::h ⇒ ς
      case Nil ⇒ ???
    }

    import PEval._

    // Rather than build a residual term, just capture the
    // history in a state.
    def rollback(h: History): History = Nil

    // split the current state, return Nil on failure
    def split(ς: State): Option[(List[State], Unsplitter[State])] = None
  }

  object W extends W
  trait W extends sc.core.sc.Whistles[Σ] {
    def isInstance(ς1: State, ς2: State): Boolean = {
      import org.bitbucket.inkytonik.kiama.util.Comparison.same
      same(ς1, ς2) || generalize(ς1, ς2).nonEmpty
    }

    def mightDiverge(ς: Σ): Boolean = ς.t match {
      case StmtT(While(_, _)) => true
      case StmtT(Call(_, _, _, _)) => true
      case StmtT(New(_, _, _)) => true
      case StmtT(Newfun(_, _, _)) => true
      case _ => false
    }

    def joinK( lhs: KStack, rhs:KStack ): Option[KStack] = {
      // continuation stacks being joined should be exactly the same
      // except perhaps different values inside FinK and ForK
      if ( lhs.κs.size == rhs.κs.size &&
        (lhs.κs zip rhs.κs).foldLeft( true )( (acc, kk) ⇒ kk match {
          case (_:FinK, _:FinK) ⇒ acc && true
          case (_:ForK, _:ForK) ⇒ acc && true
          case (x, y) if x == y ⇒ acc && true
          case _ ⇒ false
        }) ) {

        println(s"joining κs: ${lhs.κs.size} == ${rhs.κs.size}")
        Some(lhs ⊔ rhs)
      }
      else if ( lhs.κs.size > rhs.κs.size &&
        (lhs.κs.reverse zip rhs.κs.reverse).foldLeft( true )( (acc, kk) ⇒ kk match {
          case (_:FinK, _:FinK) ⇒ acc && true
          case (_:ForK, _:ForK) ⇒ acc && true
          case (x, y) if x == y ⇒ acc && true
          case _ ⇒ false
        }) ) {

        println(s"joining κs: ${lhs.κs.size} > ${rhs.κs.size}")
        Some(rhs)
      }
      else if ( lhs.κs.size < rhs.κs.size &&
        (lhs.κs.reverse zip rhs.κs.reverse).foldLeft( true )( (acc, kk) ⇒ kk match {
          case (_:FinK, _:FinK) ⇒ acc && true
          case (_:ForK, _:ForK) ⇒ acc && true
          case (x, y) if x == y ⇒ acc && true
          case _ ⇒ false
        }) ) {

        println(s"joining κs: ${lhs.κs.size} < ${rhs.κs.size}")
        Some(lhs)
      }
      else {
        println(s"not joining κs: ${lhs.κs.size} ~ ${rhs.κs.size}")
        None
      }
    }

    // Generalize two states with the same term.
    // For OmegaCFA we merge the traces by truncating to the shorter
    // trace (if one is a prefix of the other)
    def generalize(ς1: State, ς2: State): Option[State] = (ς1, ς2) match {
      case (ς1, ς2) if ς1.t == ς2.t && ς1.τ.isInstanceOf[OmegaCFA] == ς2.τ.isInstanceOf[OmegaCFA] ⇒

        val r = for {
          κs <- joinK(ς1.κs, ς2.κs)
          τ <- (ς1.τ.asInstanceOf[OmegaCFA] ⊔ ς2.τ.asInstanceOf[OmegaCFA])
        } yield ς1.copy(τ = τ, κs = κs) ⊔ ς2.copy(τ = τ, κs = κs)

        r match {
          case None =>
            println(s"trace or k merge failed")
            println(s"  prev ${ς2.τ}")
            println(s"  curr ${ς1.τ}")
            None
          case Some(ς) =>
            // When comparing, ignore local variable addresses.
            // This is a bit more conservative (but much easier) than
            // doing a lightGC before comparing the states.
            val ς1x = ς1.copy(σ = ς1.σ.copy(a2v = Map()))
            val ς2x = ς2.copy(σ = ς2.σ.copy(a2v = Map()))

            if (TagbagWhistle.isSmaller(ς2x, ς1x)) {
              // println(s"prev ${sc.util.PPAny.ugly(ς2x)}")
              println(s"<=")
              // println(s"curr ${sc.util.PPAny.ugly(ς1x)}")
              Some(ς)
            }
            else {
              println(s"prev ${sc.util.PPAny.ugly(ς2x)}")
              println(s"NOT <=")
              println(s"curr ${sc.util.PPAny.ugly(ς1x)}")
              println(s"bag(prev) = ${tagbag(ς2x)}")
              println(s"bag(curr) = ${tagbag(ς1x)}")
              None
            }
        }

      case (ς1, ς2) if ς1.t == ς2.t && ς1.τ == ς2.τ ⇒
        if (TagbagWhistle.isSmaller(ς2, ς1)) {
          Some(ς1 ⊔ ς2)
        }
        else {
          println(s"bag(prev) = ${tagbag(ς2)}")
          println(s"bag(curr) = ${tagbag(ς1)}")
          None
        }

      case _ ⇒ None
    }

    val consts: Set[Any] = Set(
      ":CONTINUE:",
      ":BREAK:",
      ":RETURN:",
      "class",
      "proto",
      "prototype",
      "class",
      "code")

    override def tagOf(a: Any): Option[Any] = a match {
      case n if (consts contains n) => Some(n)
      case n: Int if n > 3 => Some(3)
      case n: Int if n < -3 => Some(-3)
      case n: Int => Some(n)
      case n: Long if n > 3 => Some(3l)
      case n: Long if n < -3 => Some(-3l)
      case n: Long => Some(n)
      case n: Float => Some(0.0f)
      case n: Double => Some(0.0)
      case n: Char if n < 128 => Some(n)
      case n: Char => Some(128.toChar)
      case n: String => Some("string")
      case n: Boolean => Some(n)
      case n: BigInt => Some(BigInt(0))
      case n =>
        // only include syntax classes
        val x = n.getClass.getName
        if (x.startsWith("notjs.syntax.")) {
          Some(x)
        }
        // else if (x.startsWith("notjs.abstracted.domains.")) {
        //   Some(x)
        // }
        else {
          None
        }
    }

    import org.bitbucket.inkytonik.kiama.attribution.Attribution

    object A extends Attribution
    import A._

    lazy val tagbagAttr: Σ => Bag = attr {
      case ς => super.tagbag(ς)
    }

    override def tagbag(ς: Σ) = {
      tagbagAttr(ς)
    }
  }

  // Evaluator.
  // Step until either the whistle blows or we reach the Done continuation with a value.
  def supercompile(ast: Stmt): Option[Stmt] = {
    import notjs.abstracted.interpreter.Stats
    Stats.trackStats = true

    try {
      val initτ = OmegaCFA()
      val initς = Init.initState( ast, initτ )

      SC.supercompile(initς) match {
        case Some(Σ(StmtT(s), ρ, σ, ß, κs, τ)) ⇒ Some(s)
        case Some(ς) ⇒ None
        case None ⇒ None
      }
    }
    finally {
      println("STATS")
      Stats.report
    }

  }
}
