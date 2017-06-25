package scsc.js

import Trees._

// Make SCSC ASTs from Nashorn ASTs.
object MakeTrees {
  import jdk.nashorn.internal.ir
  import jdk.nashorn.internal.parser.TokenType

  import scsc.js.Visitor

  import scala.collection.mutable.ListBuffer
  import scala.collection.JavaConverters._

  implicit class JL[A](xs: java.util.List[A]) {
    def toList = xs.asScala.toList
  }

  def make(n: ir.Node): Exp = {
    val v = new TreeBuilder
    n.accept(v)
    v.peek
  }

  // Default implementation of NodeOperatorVisitor.
  // All methods are implemented uselessly mainly so we can copy-paste into
  // subclasses more easily.
  class TreeBuilder extends Visitor {
    var stack: List[Exp] = Nil

    def push(e: Exp): Unit = {
      stack = e::stack
    }

    def pop: Exp = {
      stack match {
        case e::es =>
          stack = es
          e
        case Nil =>
          ???
      }
    }

    def peek: Exp = {
      stack match {
        case e::es =>
          e
        case Nil =>
          ???
      }
    }

    // Unary leave - callback for leaving a unary +
    override def leaveADD(n: ir.UnaryNode): ir.Node = {
      val e = pop
      push(Unary(Prefix.+, e))
      n
    }

    // Unary leave - callback for leaving a unary ~
    override def leaveBIT_NOT(n: ir.UnaryNode): ir.Node = {
      val e = pop
      push(Unary(Prefix.~, e))
      n
    }



    // Unary leave - callback for leaving a ++ or -- operator
     override def leaveDECINC(n: ir.UnaryNode): ir.Node = {
       val e = pop
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
       val e = pop
       push(Delete(e))
       n
    }

    // Unary leave - callback for leaving a new operator
     override def leaveNEW(n: ir.UnaryNode): ir.Node = {
       val e = pop
       push(New(e))
       n
    }

    // Unary leave - callback for leaving a ! operator
     override def leaveNOT(n: ir.UnaryNode): ir.Node = {
       val e = pop
       push(Unary(Prefix.!, e))
       n
    }

    // Unary leave - callback for leaving a unary -
    override def leaveSUB(n: ir.UnaryNode): ir.Node = {
      val e = pop
      push(Unary(Prefix.-, e))
      n
    }

    // Unary leave - callback for leaving a typeof operator
     override def leaveTYPEOF(n: ir.UnaryNode): ir.Node = {
       val e = pop
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
       val right = pop
       val left = pop
       push(Binary(Binary.+, left, right))
       n
    }

    // Binary leave - callback for leaving a {@literal &&} operator
    override def leaveAND(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.&&, left, right))
      n
    }

    // Binary leave - callback for leaving an assignment
    override def leaveASSIGN(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.:=, left, right))
      n
    }

    // Binary leave - callback for leaving a += operator
    override def leaveASSIGN_ADD(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.+=, left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal &=} operator
    override def leaveASSIGN_BIT_AND(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.&=, left, right))
      n
    }

    // Binary leave - callback for leaving a |= operator
    override def leaveASSIGN_BIT_OR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.|=, left, right))
      n
    }

    // Binary leave - callback for leaving a ^= operator
    override def leaveASSIGN_BIT_XOR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.^=, left, right))
      n
    }

    // Binary leave - callback for leaving a /= operator
    override def leaveASSIGN_DIV(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign./=, left, right))
      n
    }

    // Binary leave - callback for leaving a %= operator
    override def leaveASSIGN_MOD(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.%=, left, right))
      n
    }

    // Binary leave - callback for leaving a *= operator
    override def leaveASSIGN_MUL(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.*=, left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal >>=} operator
    override def leaveASSIGN_SAR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.>>=, left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal <<=} operator
    override def leaveASSIGN_SHL(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.<<=, left, right))
      n
    }

    // Binary leave - callback for leaving a {@literal >>>=} operator
    override def leaveASSIGN_SHR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.>>>=, left, right))
      n
    }

    // Binary leave - callback for leaving a -= operator
    override def leaveASSIGN_SUB(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Assign(Assign.-=, left, right))
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
      val right = pop
      val left = pop
      push(Binary(Binary.&, left, right))
      n
    }

    // Binary leave - callback for leaving a | operator
    override def leaveBIT_OR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.|, left, right))
      n
    }

    // Binary leave - callback for leaving a  operator
    override def leaveBIT_XOR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.^, left, right))
      n
    }

    // Binary leave - callback for leaving a comma left operator
    override def leaveCOMMALEFT(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.COMMALEFT, left, right))
      n
    }

    // Binary leave - callback for leaving a comma left operator
    override def leaveCOMMARIGHT(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.COMMARIGHT, left, right))
      n
    }

    // Binary leave - callback for leaving a division
    override def leaveDIV(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary./, left, right))
      n
    }

    // Binary leave - callback for leaving == operator
    override def leaveEQ(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.==, left, right))
      n
    }

    // Binary leave - callback for leaving === operator
    override def leaveEQ_STRICT(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.===, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal >=} operator
    override def leaveGE(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.>=, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal >} operator
    override def leaveGT(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.>, left, right))
      n
    }

    // Binary leave - callback for leaving in operator
    override def leaveIN(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.IN, left, right))
      n
    }

    // Binary leave - callback for leaving instanceof operator
    override def leaveINSTANCEOF(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.INSTANCEOF, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal <=} operator
    override def leaveLE(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.<=, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal <} operator
    override def leaveLT(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.<, left, right))
      n
    }
    // Binary leave - callback for leaving % operator
    override def leaveMOD(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.%, left, right))
      n
    }

    // Binary leave - callback for leaving * operator
    override def leaveMUL(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.*, left, right))
      n
    }

    // Binary leave - callback for leaving != operator
    override def leaveNE(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.!=, left, right))
      n
    }

    // Binary leave - callback for leaving !== operator
    override def leaveNE_STRICT(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.!==, left, right))
      n
    }

    // Binary leave - callback for leaving || operator
    override def leaveOR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.||, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal >>} operator
    override def leaveSAR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.>>, left, right))
      n
    }

    // Binary leave - callback for leaving {@literal <<} operator
    override def leaveSHL(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.<<, left, right))
      n
    }
    // Binary leave - callback for leaving {@literal >>>} operator
    override def leaveSHR(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.>>>, left, right))
      n
    }

    // Binary leave - callback for leaving - operator
    override def leaveSUB(n: ir.BinaryNode): ir.Node = {
      val right = pop
      val left = pop
      push(Binary(Binary.-, left, right))
      n
    }

    // Callback for entering an AccessNode
    override def leaveAccessNode(n: ir.AccessNode): ir.Node = {
      val prop = pop
      val base = pop
      prop match {
        case Ident(x) =>
          push(Access(base, x))
        case _ =>
          ???
      }
      n
    }

    // Callback for leaving a Block
    override def leaveBlock(n: ir.Block): ir.Node = {
      val es = ListBuffer.empty[Exp]
      for (s <- n.getStatements.toList)
        es += pop
      push(Block(es.toList.reverse))
      n
    }

    // Callback for leaving a BreakNode
    override def leaveBreakNode(n: ir.BreakNode): ir.Node = {
      push(Break(Option(n.getLabelName)))
      n
    }

    // Callback for leaving a CallNode
    override def leaveCallNode(n: ir.CallNode): ir.Node = {
      val es = ListBuffer.empty[Exp]
      for (s <- n.getArgs.toList)
        es += pop
      val f = pop
      push(Call(f, es.toList.reverse))
      n
    }

    // Callback for leaving a CaseNode
    override def leaveCaseNode(n: ir.CaseNode): ir.Node = {
      val body = pop
      val test = pop
      push(Case(test, body))
      n
    }

    // Callback for leaving a CatchNode
    override def leaveCatchNode(n: ir.CatchNode): ir.Node = {
      val body = pop
      val test = pop
      val ex = pop
      push((Catch(ex, test, body)))
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
      push(Eval(e))
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
      val body = pop
      val modify = pop
      val test = pop
      val init = pop
      push(For(init, test, modify, body))
      n
    }

    // Callback for leaving a FunctionNode
    override def leaveFunctionNode(n: ir.FunctionNode): ir.Node = {
      val body = pop

      val xs = ListBuffer.empty[Name]
      for (s <- n.getParameters.toList) {
        val x = pop
        x match {
          case Ident(x) =>
            xs += x
          case _ =>
            ???
        }
      }

      if (n.getIdent == null) {
        Lambda(xs.toList.reverse, body)
      }
      else {
        val x = pop
        x match {
          case Ident(x) =>
            FunDef(x, xs.toList.reverse, body)
          case _ =>
            ???
        }
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
      push(Ident(n.getName))
      n
    }

    // Callback for leaving an IfNode
    override def leaveIfNode(n: ir.IfNode): ir.Node = {
      if (n.getFail != null) {
        val f = pop
        val t = pop
        val c = pop
        push(IfElse(c, t, f))
      }
      else {
        val t = pop
        val c = pop
        push(IfThen(c, t))
      }
      n
    }

    // Callback for leaving an IndexNode
    override def leaveIndexNode(n: ir.IndexNode): ir.Node = {
      val i = pop
      val a = pop
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
      val x = pop
      x match {
        case Ident(x) =>
          push(Label(x, e))
        case _ =>
          ???
      }
      n
    }

    // Callback for leaving a LiteralNode
    override def leaveLiteralNode(n: ir.LiteralNode[_]): ir.Node = {
      import jdk.nashorn.internal.runtime.ScriptRuntime

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
        case _ =>
          ???
      }
      n
    }

    // Callback for leaving an ObjectNode
    override def leaveObjectNode(n: ir.ObjectNode): ir.Node = {
      val es = ListBuffer.empty[Exp]
      for (s <- n.getElements.toList)
        es += pop
      push(ObjectLit(es.toList.reverse))
      n
    }

    // Callback for leaving a PropertyNode
    override def leavePropertyNode(n: ir.PropertyNode): ir.Node = {
      val v = pop
      val k = pop
      push(Property(k, v))
      n
    }

    override def leaveReturnNode(n: ir.ReturnNode): ir.Node = {
      if (n.isReturn) {
        if (n.getExpression != null) {
          val e = pop
          push(Return(Some(e)))
        }
        else {
          push(Return(None))
        }
      }
      else if (n.isYield) {
        if (n.getExpression != null) {
          val e = pop
          push(Yield(Some(e)))
        }
        else {
          push(Yield(None))
        }
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
      val e = pop
      push(Switch(e, es.toList.reverse))
      n
    }

    // Callback for leaving a TernaryNode
    override def leaveTernaryNode(n: ir.TernaryNode): ir.Node = {
      val f = pop
      val t = pop
      val c = pop
      push(Cond(c, t, f))
      n
    }

    // Callback for leaving a ThrowNode
    override def leaveThrowNode(n: ir.ThrowNode): ir.Node = {
      val e = pop
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
      val es = ListBuffer.empty[Exp]
      for (s <- n.getCatchBlocks.toList) {
        val c = pop
        c match {
          case Catch(_, _, _) =>
            es += c
          case _ =>
            ???
        }
      }
      val e = pop
      push(Try(e, es.toList.reverse, f))
      n
    }

    // Callback for leaving a {@link JoinPredecessorExpression}.
    override def leaveJoinPredecessorExpression(n: ir.JoinPredecessorExpression): ir.Node = {
      leaveDefault(n)
      n
    }

    // Callback for leaving a VarNode
    override def leaveVarNode(n: ir.VarNode): ir.Node = {
      val e = {
        if (n.getInit != null) {
          val v = pop
          Some(v)
        }
        else {
          None
        }
      }
      val x = pop
      x match {
        case Ident(x) =>
          if (n.isLet) {
            push(LetDef(x, e))
          }
          else if (n.isConst) {
            push(ConstDef(x, e))
          }
          else {
            push(VarDef(x, e))
          }
        case _ =>
          ???
      }
      n
    }

    // Callback for leaving a WhileNode
    override def leaveWhileNode(n: ir.WhileNode): ir.Node = {
      if (n.isDoWhile) {
        val cond = pop
        val body = pop
        push(DoWhile(body, cond))
      }
      else {
        val body = pop
        val cond = pop
        push(While(cond, body))
      }
      n
    }

    // Callback for leaving a WithNode
    override def leaveWithNode(n: ir.WithNode): ir.Node = {
      val body = pop
      val e = pop
      push(With(e, body))
      n
    }
  }
}