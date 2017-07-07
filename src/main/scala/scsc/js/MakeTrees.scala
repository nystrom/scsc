package scsc.js

import Trees._

// Make SCSC ASTs from Nashorn ASTs.
object MakeTrees {
  import jdk.nashorn.internal.ir
  import jdk.nashorn.internal.parser.TokenType

  import scsc.js.Visitor
  import scsc.util.FreshVar

  import scala.collection.mutable.ListBuffer
  import scala.collection.JavaConverters._

  implicit class JL[A](xs: java.util.List[A]) {
    def toList = xs.asScala.toList
  }

  object Debug extends Visitor {
    override def enterDefault(n: ir.Node) = {
      println(s"enter ${n.getClass.getName} $n")
      super.enterDefault(n)
    }
    override def leaveDefault(n: ir.Node) = {
      println(s"leave ${n.getClass.getName} $n")
      super.leaveDefault(n)
    }
  }

  class Flatten() extends TreeWalk.Rewriter {
    val hoist: ListBuffer[Exp] = ListBuffer()

    def block(es: List[Exp]) = es match {
      case Nil => Undefined()
      case e::es => es.foldLeft(e) {
        case (e1, e2) => Seq(e1, e2)
      }
    }

    override def rewrite(e: Exp) = e match {
      case Binary(op, e1, e2) =>
        val t = FreshVar()
        val t1 = rewrite(e1)
        val t2 = rewrite(e2)
        hoist += Assign(None, LocalAddr(t), Binary(op, t1, t2))
        Local(t)
      case Unary(op, e1) =>
        val t = FreshVar()
        val t1 = rewrite(e1)
        hoist += Assign(None, LocalAddr(t), Unary(op, t1))
        Local(t)
      case Delete(e1) =>
        val t = FreshVar()
        val t1 = rewrite(e1)
        hoist += Assign(None, LocalAddr(t), Delete(t1))
        Local(t)
      case Typeof(e1) =>
        val t = FreshVar()
        val t1 = rewrite(e1)
        hoist += Assign(None, LocalAddr(t), Typeof(t1))
        Local(t)
      case Void(e1) =>
        val t = FreshVar()
        val t1 = rewrite(e1)
        hoist += Assign(None, LocalAddr(t), Void(t1))
        Local(t)
      case Assign(op, e1, e2) =>
        val t = FreshVar()
        val t1 = rewrite(e1)
        val t2 = rewrite(e2)
        Assign(op, t1, t2)
      case Cond(e0, e1, e2) =>
        val t = FreshVar()
        val t0 = rewrite(e0)
        val v1 = new Flatten()
        val v2 = new Flatten()
        val t1 = v1.rewrite(e1)
        val t2 = v2.rewrite(e2)
        hoist += IfElse(t0, block(v1.hoist.toList :+ Assign(None, LocalAddr(t), t1)), block(v2.hoist.toList :+ Assign(None, LocalAddr(t), t2)))
        Local(t)
      case IfElse(e0, s1, s2) =>
        val t0 = rewrite(e0)
        val v1 = new Flatten()
        val v2 = new Flatten()
        val t1 = v1.rewrite(s1)
        val t2 = v2.rewrite(s2)
        IfElse(t0, block(v1.hoist.toList :+ t1), block(v2.hoist.toList :+ t2))
      case Value(v) =>
        v
      case e =>
        super.rewrite(e)
    }
  }

  // Hoist variable definitions to the top of the scope.
  // Replace variable definitions with assignments or with nothing if a lambda.
  // Add assignments to nodes that might create objects
  // This should ensure new objects become reachable from the environment
  // in a finite number of steps.
  object IntroAssignments extends TreeWalk.Rewriter {
    val hoist: ListBuffer[Exp] = ListBuffer()

    override def rewrite(e: Exp) = e match {
      // case _: ObjectLit | _: ArrayLit | _: Call | _: NewCall | _: Lambda =>
      //   println(s"INTRO assignment for $e")
      //   val e2 = super.rewrite(e)
      //   val x = FreshVar()
      //   hoist += VarDef(x, Undefined())
      //   Assign(None, LocalAddr(x), e2)
      case e @ VarDef(x, Lambda(xs, body)) =>
        println(s"HOIST function def $e")
        val body2 = super.rewrite(body)
        hoist += VarDef(x, Lambda(xs, body2))
        Undefined()
      case e @ VarDef(x, init) =>
        println(s"HOIST var def $e")
        val e2 = super.rewrite(e)
        hoist += VarDef(x, Undefined())
        Seq(Assign(None, LocalAddr(x), init), Undefined())
      case e @ Scope(body) =>
        println(s"rewrite scope $e")
        val oldHoist = hoist.toList
        hoist.clear
        val body2 = rewrite(body)
        val body3 = hoist.toList.foldRight(body2) {
          case (d, e) => Seq(d, e)
        }
        hoist.clear
        hoist ++= oldHoist
        Scope(body3)
      case e =>
        super.rewrite(e)
    }
  }

  def make(n: ir.Node): Option[Scope] = {
    n.accept(Debug)

    val v = new TreeBuilder
    n.accept(v)
    v.peek flatMap {
      case p: Scope =>
        v.pop
        v.peek match {
          case Some(_) =>
            println(s"stack not empty: $v.stack")
          case None =>
            // ok
        }
        Some(p)
      case _ =>
        println("Scope is not at top of stack")
        None
    }
  }

  def desugar(p: Scope) = {
    IntroAssignments.rewrite(p).asInstanceOf[Scope]
  }

  // Default implementation of NodeOperatorVisitor.
  // All methods are implemented uselessly mainly so we can copy-paste into
  // subclasses more easily.
  class TreeBuilder extends Visitor {
    var stack: List[Exp] = Nil

    // Wrap e in an explicit load expression.
    def lvalue(e: Exp): Exp = e match {
      // The following expressions evaluate to addresses and should be wrapped in a load.
      case Local(x) => LocalAddr(x)
      case Index(a, i) => IndexAddr(a, i)
      case e => e
    }

    def push(e: Exp): Unit = {
      println(s"push $e")
      stack = e::stack
    }

    def pop: Exp = {
      stack match {
        case e::es =>
          stack = es
          println(s"pop $e")
          e
        case Nil =>
          println(s"stack empty")
          ???
      }
    }

    def popR = pop
    def popL = lvalue(pop)

    def peek: Option[Exp] = stack.headOption

    override def leaveDefault(n: ir.Node): ir.Node = {
      println(s"unimplemented ${n.getClass.getName}")
      n
    }

    // Unary leave - callback for leaving a unary +
    override def leaveADD(n: ir.UnaryNode): ir.Node = {
      val e = popR
      push(Unary(Prefix.+, e))
      n
    }

    // Unary leave - callback for leaving a unary ~
    override def leaveBIT_NOT(n: ir.UnaryNode): ir.Node = {
      val e = popR
      push(Unary(Prefix.~, e))
      n
    }

    // Unary leave - callback for leaving a ++ or -- operator
    override def leaveDECINC(n: ir.UnaryNode): ir.Node = {
      val e = popL
      val op = n.tokenType match {
        case TokenType.DECPREFIX =>
          Prefix.--
        case TokenType.INCPREFIX =>
          Prefix.++
        case TokenType.DECPOSTFIX =>
          Postfix.--
        case TokenType.INCPOSTFIX =>
          Postfix.++
        case _ =>
          ???
      }
      push(IncDec(op, e))
      n
    }

    // Unary leave - callback for leaving a delete operator
    override def leaveDELETE(n: ir.UnaryNode): ir.Node = {
      val e = popL
      push(Delete(e))
      n
    }

    // Unary leave - callback for leaving a new operator
    override def leaveNEW(n: ir.UnaryNode): ir.Node = {
      val e = pop
      e match {
        case NewCall(f, args) =>
          push(e)
        case Call(f, args) =>
          push(NewCall(f, args))
        case e =>
          push(NewCall(e, Nil))
      }
      n
    }

    // Unary leave - callback for leaving a ! operator
    override def leaveNOT(n: ir.UnaryNode): ir.Node = {
      val e = popR
      push(Unary(Prefix.!, e))
      n
    }

    // Unary leave - callback for leaving a unary -
    override def leaveSUB(n: ir.UnaryNode): ir.Node = {
      val e = popR
      push(Unary(Prefix.-, e))
      n
    }

    // Unary leave - callback for leaving a typeof operator
    override def leaveTYPEOF(n: ir.UnaryNode): ir.Node = {
      val e = popR
      push(Typeof(e))
      n
    }

    // Unary leave - callback for leaving a void
    override def leaveVOID(n: ir.UnaryNode): ir.Node = {
      val e = pop
      push(Void(e))
      n
    }

    // Binary leave - callback for leaving a + operator
    override def leaveADD(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.+, left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal &&} operator
    override def leaveAND(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.&&, left, right))
      n
    }

    // Binary leave - callback for leaving an assignment
    override def leaveASSIGN(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(None, left, right))
      n
    }

    // Binary leave - callback for leaving a += operator
    override def leaveASSIGN_ADD(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.+), left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal &=} operator
    override def leaveASSIGN_BIT_AND(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.&), left, right))
      n
    }

    // Binary leave - callback for leaving a |= operator
    override def leaveASSIGN_BIT_OR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.|), left, right))
      n
    }

    // Binary leave - callback for leaving a ^= operator
    override def leaveASSIGN_BIT_XOR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.^), left, right))
      n
    }

    // Binary leave - callback for leaving a /= operator
    override def leaveASSIGN_DIV(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary./), left, right))
      n
    }

    // Binary leave - callback for leaving a %= operator
    override def leaveASSIGN_MOD(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.%), left, right))
      n
    }

    // Binary leave - callback for leaving a *= operator
    override def leaveASSIGN_MUL(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.*), left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal >>=} operator
    override def leaveASSIGN_SAR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.>>), left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal <<=} operator
    override def leaveASSIGN_SHL(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.<<), left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal >>>=} operator
    override def leaveASSIGN_SHR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.>>>), left, right))
      n
    }

    // Binary leave - callback for leaving a -= operator
    override def leaveASSIGN_SUB(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popL
      push(Assign(Some(Binary.-), left, right))
      n
    }

    // Binary leave - callback for leaving a bind operator
    override def leaveBIND(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.BIND, left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal &} operator
    override def leaveBIT_AND(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.&, left, right))
      n
    }

    // Binary leave - callback for leaving a | operator
    override def leaveBIT_OR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.|, left, right))
      n
    }

    // Binary leave - callback for leaving a  operator
    override def leaveBIT_XOR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.^, left, right))
      n
    }

    // Binary leave - callback for leaving a comma left operator
    override def leaveCOMMALEFT(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.COMMALEFT, left, right))
      n
    }

    // Binary leave - callback for leaving a comma left operator
    override def leaveCOMMARIGHT(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.COMMARIGHT, left, right))
      n
    }

    // Binary leave - callback for leaving a division
    override def leaveDIV(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary./, left, right))
      n
    }

    // Binary leave - callback for leaving == operator
    override def leaveEQ(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.==, left, right))
      n
    }

    // Binary leave - callback for leaving === operator
    override def leaveEQ_STRICT(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.===, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal >=} operator
    override def leaveGE(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.>=, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal >} operator
    override def leaveGT(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.>, left, right))
      n
    }

    // Binary leave - callback for leaving in operator
    override def leaveIN(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.IN, left, right))
      n
    }

    // Binary leave - callback for leaving instanceof operator
    override def leaveINSTANCEOF(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.INSTANCEOF, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal <=} operator
    override def leaveLE(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.<=, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal <} operator
    override def leaveLT(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.<, left, right))
      n
    }
    // Binary leave - callback for leaving % operator
    override def leaveMOD(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.%, left, right))
      n
    }

    // Binary leave - callback for leaving * operator
    override def leaveMUL(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.*, left, right))
      n
    }

    // Binary leave - callback for leaving != operator
    override def leaveNE(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.!=, left, right))
      n
    }

    // Binary leave - callback for leaving !== operator
    override def leaveNE_STRICT(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.!==, left, right))
      n
    }

    // Binary leave - callback for leaving || operator
    override def leaveOR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.||, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal >>} operator
    override def leaveSAR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.>>, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal <<} operator
    override def leaveSHL(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.<<, left, right))
      n
    }
    // Binary leave - callback for leaving {@literal >>>} operator
    override def leaveSHR(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.>>>, left, right))
      n
    }

    // Binary leave - callback for leaving - operator
    override def leaveSUB(n: ir.BinaryNode): ir.Node = {
      val right = popR
      val left = popR
      push(Binary(Binary.-, left, right))
      n
    }

    // Callback for entering an AccessNode
    override def leaveAccessNode(n: ir.AccessNode): ir.Node = {
      val prop = n.getProperty
      val base = popR
      push(Index(base, StringLit(prop)))
      // val prop = pop
      // val base = popR
      // prop match {
      //   case Local(x) =>
      //     push(Access(base, x))
      //   case _ =>
      //     ???
      // }
      n
    }

    // Callback for leaving a Block
    override def leaveBlock(n: ir.Block): ir.Node = {
      val es = ListBuffer.empty[Exp]
      for (s <- n.getStatements.toList)
        es += pop
      val block = es.toList.reverse match {
        case Nil => Empty()
        case s::ss =>
          ss.foldLeft(s) {
            case (s1, s2) => Seq(s1, s2)
          }
      }
      push(block)
      n
    }

    // object FloatDefs extends Rewriter {
    //   override def rewriteM(e: Exp) = super.rewriteM(e) match {
    //     case Lambda(xs, e) =>
    //
    //     case Block(ss) =>
    //       val defs = ss collect {
    //         case VarDef(x, e) =>
    //           VarDef(x, Undefined())
    //       }
    //       val ss2 = ss map {
    //         case VarDef(x, e) =>
    //           Assign(None, LocalAddr(x), e)
    //         case s =>
    //           s
    //       }
    //       Block(defs ++ ss2)
    //     case e =>
    //       e
    //   }
    // }

    // Callback for leaving a BreakNode
    override def leaveBreakNode(n: ir.BreakNode): ir.Node = {
      push(Break(Option(n.getLabelName)))
      n
    }

    // Callback for leaving a CallNode
    override def leaveCallNode(n: ir.CallNode): ir.Node = {
      // If the node has an EvalArgs child, pop its children from the stack.
      if (n.getEvalArgs != null) {
        val evalThis = pop
        val evalCode = pop
        ()
      }
      val es = ListBuffer.empty[Exp]
      for (s <- n.getArgs.toList)
        es += popR
      val f = popR
      if (n.isNew)
        push(NewCall(f, es.toList.reverse))
      else
        push(Call(f, es.toList.reverse))
      n
    }

    // Callback for leaving a CaseNode
    override def leaveCaseNode(n: ir.CaseNode): ir.Node = {
      if (n.getTest != null && n.getBody != null) {
        val body = pop
        val test = popR
        push(Case(Some(test), body))
      }
      else if (n.getBody != null) {
        val body = pop
        push(Case(None, body))
      }
      else if (n.getTest != null) {
        val test = popR
        push(Case(Some(test), Empty()))
      }
      else {
        push(Case(None, Empty()))
      }
      n
    }

    // Callback for leaving a CatchNode
    override def leaveCatchNode(n: ir.CatchNode): ir.Node = {
      if (n.getExceptionCondition != null) {
        val body = pop
        val test = popR
        val ex = pop
        ex match {
          case Local(x) =>
            push((Catch(x, Some(test), body)))
          case _ =>
            ???
        }
      }
      else {
        val body = pop
        val ex = pop
        ex match {
          case Local(x) =>
            push((Catch(x, None, body)))
          case _ =>
            ???
        }
      }
      n
    }

    // Callback for leaving a ContinueNode
    override def leaveContinueNode(n: ir.ContinueNode): ir.Node = {
      push(Continue(Option(n.getLabelName)))
      n
    }

    // Callback for leaving an EmptyNode
    override def leaveEmptyNode(n: ir.EmptyNode): ir.Node = {
      push(Empty())
      n
    }

    // Callback for leaving an ExpressionStatement
    override def leaveExpressionStatement(n: ir.ExpressionStatement): ir.Node = {
      val e = pop
      push(e)
      n
    }

    // Callback for leaving a BlockStatement
    override def leaveBlockStatement(n: ir.BlockStatement): ir.Node = {
      val e = pop
      push(e)
      n
    }

    // Callback for leaving a ForNode
    override def leaveForNode(n: ir.ForNode): ir.Node = {
      if (n.isForIn) {
        val body = pop
        val modify = Option(n.getModify) map { _ => pop } getOrElse Empty()
        // val test = Option(n.getTest) map { _ => popR } getOrElse Bool(true)
        // println(s"test ${n.getTest} $test")
        val init = Option(n.getInit) map { _ => pop } getOrElse Empty()
        push(ForIn(None, init, modify, body))
      }
      else {
        val body = pop
        val modify = Option(n.getModify) map { _ => pop } getOrElse Empty()
        val test = Option(n.getTest) map { _ => popR } getOrElse Bool(true)
        val init = Option(n.getInit) map { _ => pop } getOrElse Empty()
        if (n.isForEach) {
          push(ForEach(None, init, test, modify, body))
        }
        else {
          push(For(None, init, test, modify, body))
        }
      }
      n
    }

    // Callback for leaving a FunctionNode
    override def leaveFunctionNode(n: ir.FunctionNode): ir.Node = {
      val body = pop

      val xs = ListBuffer.empty[Name]
      for (s <- n.getParameters.toList) {
        xs += s.getName
      }

      if (n.isProgram) {
        assert(xs.isEmpty)
        push(Scope(body))
      }
      else {
        push(Lambda(xs.toList, Scope(body)))
      }
      n
    }

    // Callback for leaving a {@link GetSplitState}.
    override def leaveGetSplitState(n: ir.GetSplitState): ir.Node = {
      leaveDefault(n)
      n
    }

    // Callback for leaving an IdentNode
    override def leaveIdentNode(n: ir.IdentNode): ir.Node = {
      push(Local(n.getName))
      n
    }

    // Callback for leaving an IfNode
    override def leaveIfNode(n: ir.IfNode): ir.Node = {
      if (n.getFail != null) {
        val f = pop
        val t = pop
        val c = popR
        push(IfElse(c, t, f))
      }
      else {
        val t = pop
        val c = popR
        push(IfElse(c, t, Undefined()))
      }
      n
    }

    // Callback for leaving an IndexNode
    override def leaveIndexNode(n: ir.IndexNode): ir.Node = {
      val i = popR
      val a = popR
      push(Index(a, i))
      n
    }

    // Callback for leaving a JumpToInlinedFinally
    override def leaveJumpToInlinedFinally(n: ir.JumpToInlinedFinally): ir.Node = {
      leaveDefault(n)
      n
    }

    // Callback for leaving a LabelNode
    override def leaveLabelNode(n: ir.LabelNode): ir.Node = {
      val e = pop
      val x = n.getLabelName
      e match {
        case ForIn(None, init, modify, body) =>
          push(ForIn(Some(x), init, modify, body))
        case ForEach(None, init, test, modify, body) =>
          push(ForEach(Some(x), init, test, modify, body))
        case For(None, init, test, modify, body) =>
          push(For(Some(x), init, test, modify, body))
        case DoWhile(None, test, body) =>
          push(DoWhile(Some(x), test, body))
        case While(None, body, test) =>
          push(While(Some(x), body, test))
        case s =>
          push(DoWhile(Some(x), s, Bool(false)))
      }
      n
    }

    // Callback for leaving a LiteralNode
    override def leaveLiteralNode(n: ir.LiteralNode[_]): ir.Node = {
      import jdk.nashorn.internal.runtime.ScriptRuntime
      import jdk.nashorn.internal.parser.Lexer.RegexToken
      import jdk.nashorn.internal.parser.Lexer.XMLToken

      n.getValue match {
        case null =>
          push(Null())
        case v: Array[_] =>
          val es = ListBuffer.empty[Exp]
          for (s <- v)
            es += pop
          push(ArrayLit(es.toList.reverse))
        case v: Double =>
          push(Num(v))
        case v: Int =>
          push(Num(v.toDouble))
        case v: Long =>
          push(Num(v.toDouble))
        case v: String =>
          push(StringLit(v))
        case v: Boolean =>
          push(Bool(v))
        case ScriptRuntime.UNDEFINED =>
          push(Undefined())
        case v: RegexToken =>
          push(Regex(v.getExpression, v.getOptions))
        case v: XMLToken =>
          push(XML(v.getExpression))
        case v =>
          println(s"missing implementation $v ${v.getClass}")
          ???
      }
      n
    }

    // Callback for leaving an ObjectNode
    override def leaveObjectNode(n: ir.ObjectNode): ir.Node = {
      val es = ListBuffer.empty[Exp]
      for (s <- n.getElements.toList) {
        val p = pop
        p match {
          case p: Property =>
            es += p
          case _ =>
            ???
        }
      }
      push(ObjectLit(es.toList.reverse))
      n
    }

    // Callback for leaving a PropertyNode
    override def leavePropertyNode(n: ir.PropertyNode): ir.Node = {
      val setter = Option(n.getSetter) map { _ => pop }
      val getter = Option(n.getGetter) map { _ => pop }
      val v = Option(n.getValue) map { _ => pop } getOrElse Undefined()
      val k = pop
      // val k = n.getKeyName
      // push(Property(StringLit(k), v, getter, setter))
      k match {
        case Local(x) =>
          push(Property(StringLit(x), v, getter, setter))
        case k =>
          push(Property(k, v, getter, setter))
      }
      n
    }

    override def leaveReturnNode(n: ir.ReturnNode): ir.Node = {
      if (n.isReturn) {
        val e = Option(n.getExpression) map { _ => popR }
        push(Return(e))
      }
      else if (n.isYield) {
        val e = Option(n.getExpression) map { _ => popR }
        push(Yield(e))
      }
      else {
        ???
      }
      n
    }
    // Callback for leaving a RuntimeNode
    override def leaveRuntimeNode(n: ir.RuntimeNode): ir.Node = {
      leaveDefault(n)
      n
    }

    // Callback for leaving a {@link SetSplitState}.
    override def leaveSetSplitState(n: ir.SetSplitState): ir.Node = {
      leaveDefault(n)
      n
    }

    // Callback for leaving a SplitNode
    override def leaveSplitNode(n: ir.SplitNode): ir.Node = {
      leaveDefault(n)
      n
    }

    // Callback for leaving a SplitReturn
    override def leaveSplitReturn(n: ir.SplitReturn): ir.Node = {
      leaveDefault(n)
      n
    }

    // Callback for leaving a SwitchNode
    override def leaveSwitchNode(n: ir.SwitchNode): ir.Node = {
      val es = ListBuffer.empty[Exp]
      for (s <- n.getCases.toList) {
        val c = pop
        c match {
          case Case(_, _) =>
            es += c
          case _ =>
            ???
        }
      }
      val e = popR
      push(Switch(e, es.toList.reverse))
      n
    }

    // Callback for leaving a TernaryNode
    override def leaveTernaryNode(n: ir.TernaryNode): ir.Node = {
      val f = popR
      val t = popR
      val c = popR
      push(Cond(c, t, f))
      n
    }

    // Callback for leaving a ThrowNode
    override def leaveThrowNode(n: ir.ThrowNode): ir.Node = {
      val e = popR
      push(Throw(e))
      n
    }

    // Callback for leaving a TryNode
    override def leaveTryNode(n: ir.TryNode): ir.Node = {
      val f = {
        if (n.getFinallyBody == null)
          None
        else {
          val v = pop
          Some(v)
        }
      }
      val es = ListBuffer.empty[Catch]
      for (s <- n.getCatchBlocks.toList) {
        val c = pop
        c match {
          case c @ Catch(_, _, _) =>
            es += c
          case _ =>
            ???
        }
      }
      val e = pop
      val e2 = f match {
        case Some(v) =>
          TryFinally(e, v)
        case None =>
          e
      }
      val cs2 = f match {
        case Some(v) =>
          es.toList.reverse map {
            case Catch(ex, test, body) =>
              Catch(ex, test, TryFinally(body, v))
          }
        case None =>
          es.toList.reverse
      }
      cs2 match {
        case Nil => push(e2)
        case cs2 => push(TryCatch(e2, cs2))
      }
      n
    }

    // Callback for leaving a {@link JoinPredecessorExpression}.
    override def leaveJoinPredecessorExpression(n: ir.JoinPredecessorExpression): ir.Node = {
      val e = pop
      push(e)
      n
    }

    // Callback for leaving a VarNode
    override def leaveVarNode(n: ir.VarNode): ir.Node = {
      // For some reason, the name is on top of the stack and the initializer is below it
      // rather than the other way around.
      val x = pop
      val e = Option(n.getInit) map { _ => popR } getOrElse Undefined()
      x match {
        case Local(x) =>
          push(VarDef(x, e))
        case _ =>
          ???
      }
      n
    }

    // Callback for leaving a WhileNode
    override def leaveWhileNode(n: ir.WhileNode): ir.Node = {
      if (n.isDoWhile) {
        val test = popR
        val body = pop
        push(DoWhile(None, body, test))
      }
      else {
        val body = pop
        val test = popR
        push(While(None, test, body))
      }
      n
    }

    // Callback for leaving a WithNode
    override def leaveWithNode(n: ir.WithNode): ir.Node = {
      val body = pop
      val exp = popR
      push(With(exp, body))
      n
    }
  }
}
