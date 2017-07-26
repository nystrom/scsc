package sc.js.syntax

import jdk.nashorn.internal.ir.visitor._
import jdk.nashorn.internal.ir._

// Default implementation of NodeOperatorVisitor.
// All methods are implemented uselessly mainly so we can copy-paste into
// subclasses more easily.
class NashornVisitor extends NodeOperatorVisitor[LexicalContext](new LexicalContext) {
  protected override def enterDefault(node: Node): Boolean = true
  protected override def leaveDefault(node: Node): Node = node

  // Unary enter - callback for entering a unary +
  override def enterADD(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a unary +
  override def leaveADD(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Unary enter - callback for entering a ~ operator
  override def enterBIT_NOT(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a unary ~
  override def leaveBIT_NOT(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Unary enter - callback for entering a ++ or -- operator
  override def enterDECINC(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a ++ or -- operator
   override def leaveDECINC(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Unary enter - callback for entering a delete operator
  override def enterDELETE(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a delete operator
   override def leaveDELETE(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Unary enter - callback for entering a new operator
  override def enterNEW(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a new operator
   override def leaveNEW(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Unary enter - callback for entering a ! operator
  override def enterNOT(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a ! operator
   override def leaveNOT(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Unary enter - callback for entering a unary -
  override def enterSUB(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a unary -
  override def leaveSUB(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Unary enter - callback for entering a typeof
  override def enterTYPEOF(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a typeof operator
   override def leaveTYPEOF(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Unary enter - callback for entering a void
  override def enterVOID(unaryNode: UnaryNode): Boolean = {
    enterDefault(unaryNode)
  }

  // Unary leave - callback for leaving a void
   override def leaveVOID(unaryNode: UnaryNode): Node = {
    leaveDefault(unaryNode)
  }

  // Binary enter - callback for entering + operator
  override def enterADD(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a + operator
   override def leaveADD(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal &&} operator
  override def enterAND(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a {@literal &&} operator
  override def leaveAND(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering an assignment
  override def enterASSIGN(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving an assignment
  override def leaveASSIGN(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering += operator
  override def enterASSIGN_ADD(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a += operator
  override def leaveASSIGN_ADD(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal &=} operator
  override def enterASSIGN_BIT_AND(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a {@literal &=} operator
  override def leaveASSIGN_BIT_AND(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering |= operator
  override def enterASSIGN_BIT_OR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a |= operator
  override def leaveASSIGN_BIT_OR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering ^= operator
  override def enterASSIGN_BIT_XOR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a ^= operator
  override def leaveASSIGN_BIT_XOR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering /= operator
  override def enterASSIGN_DIV(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a /= operator
  override def leaveASSIGN_DIV(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering %= operator
  override def enterASSIGN_MOD(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a %= operator
  override def leaveASSIGN_MOD(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering *= operator
  override def enterASSIGN_MUL(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a *= operator
  override def leaveASSIGN_MUL(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal >>=} operator
  override def enterASSIGN_SAR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a {@literal >>=} operator
  override def leaveASSIGN_SAR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering a {@literal <<=} operator
  override def enterASSIGN_SHL(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a {@literal <<=} operator
  override def leaveASSIGN_SHL(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal >>>=} operator
  override def enterASSIGN_SHR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a {@literal >>>=} operator
  override def leaveASSIGN_SHR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering -= operator
  override def enterASSIGN_SUB(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a -= operator
  override def leaveASSIGN_SUB(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering a bind operator
  override def enterBIND(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a bind operator
  override def leaveBIND(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal &} operator
  override def enterBIT_AND(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a {@literal &} operator
  override def leaveBIT_AND(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering | operator
  override def enterBIT_OR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a | operator
  override def leaveBIT_OR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering ^ operator
  override def enterBIT_XOR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a  operator
  override def leaveBIT_XOR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering comma left operator
  override def enterCOMMALEFT(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a comma left operator
  override def leaveCOMMALEFT(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering comma right operator
  override def enterCOMMARIGHT(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a comma left operator
  override def leaveCOMMARIGHT(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering a division
  override def enterDIV(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving a division
  override def leaveDIV(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering == operator
  override def enterEQ(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving == operator
  override def leaveEQ(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering === operator
  override def enterEQ_STRICT(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving === operator
  override def leaveEQ_STRICT(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal >=} operator
  override def enterGE(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving {@literal >=} operator
  override def leaveGE(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal >} operator
  override def enterGT(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving {@literal >} operator
  override def leaveGT(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering in operator
  override def enterIN(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving in operator
  override def leaveIN(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering instanceof operator
  override def enterINSTANCEOF(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving instanceof operator
  override def leaveINSTANCEOF(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal <=} operator
  override def enterLE(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving {@literal <=} operator
  override def leaveLE(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal <} operator
  override def enterLT(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving {@literal <} operator
  override def leaveLT(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }
  // Binary enter - callback for entering % operator
  override def enterMOD(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving % operator
  override def leaveMOD(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering * operator
  override def enterMUL(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving * operator
  override def leaveMUL(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering != operator
  override def enterNE(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving != operator
  override def leaveNE(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering a !== operator
  override def enterNE_STRICT(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving !== operator
  override def leaveNE_STRICT(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering || operator
  override def enterOR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving || operator
  override def leaveOR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal >>} operator
  override def enterSAR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving {@literal >>} operator
  override def leaveSAR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering {@literal <<} operator
  override def enterSHL(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving {@literal <<} operator
  override def leaveSHL(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }
  // Binary enter - callback for entering {@literal >>>} operator
  override def enterSHR(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving {@literal >>>} operator
  override def leaveSHR(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Binary enter - callback for entering - operator
  override def enterSUB(binaryNode: BinaryNode): Boolean = {
    enterDefault(binaryNode)
  }

  // Binary leave - callback for leaving - operator
  override def leaveSUB(binaryNode: BinaryNode): Node = {
    leaveDefault(binaryNode)
  }

  // Callback for entering an AccessNode
  override def enterAccessNode(accessNode: AccessNode): Boolean = {
    enterDefault(accessNode)
  }

  // Callback for entering an AccessNode
  override def leaveAccessNode(accessNode: AccessNode): Node = {
    leaveDefault(accessNode)
  }

  // Callback for entering a Block
  override def enterBlock(block: Block): Boolean = {
    enterDefault(block)
  }

  // Callback for leaving a Block
  override def leaveBlock(block: Block): Node = {
    leaveDefault(block)
  }

  // Callback for entering a BreakNode
  override def enterBreakNode(breakNode: BreakNode): Boolean = {
    enterDefault(breakNode)
  }

  // Callback for leaving a BreakNode
  override def leaveBreakNode(breakNode: BreakNode): Node = {
    leaveDefault(breakNode)
  }

  // Callback for entering a CallNode
  override def enterCallNode(callNode: CallNode): Boolean = {
    enterDefault(callNode)
  }

  // Callback for leaving a CallNode
  override def leaveCallNode(callNode: CallNode): Node = {
    leaveDefault(callNode)
  }

  // Callback for entering a CaseNode
  override def enterCaseNode(caseNode: CaseNode): Boolean = {
    enterDefault(caseNode)
  }

  // Callback for leaving a CaseNode
  override def leaveCaseNode(caseNode: CaseNode): Node = {
    leaveDefault(caseNode)
  }

  // Callback for entering a CatchNode
  override def enterCatchNode(catchNode: CatchNode): Boolean = {
    enterDefault(catchNode)
  }

  // Callback for leaving a CatchNode
  override def leaveCatchNode(catchNode: CatchNode): Node = {
    leaveDefault(catchNode)
  }

  // Callback for entering a ContinueNode
  override def enterContinueNode(continueNode: ContinueNode): Boolean = {
    enterDefault(continueNode)
  }

  // Callback for leaving a ContinueNode
  override def leaveContinueNode(continueNode: ContinueNode): Node = {
    leaveDefault(continueNode)
  }

  // Callback for entering an EmptyNode
  override def enterEmptyNode(emptyNode: EmptyNode): Boolean = {
    enterDefault(emptyNode)
  }

  // Callback for leaving an EmptyNode
  override def leaveEmptyNode(emptyNode: EmptyNode): Node = {
    leaveDefault(emptyNode)
  }

  // Callback for entering an ExpressionStatement
  override def enterExpressionStatement(expressionStatement: ExpressionStatement): Boolean = {
    enterDefault(expressionStatement)
  }

  // Callback for leaving an ExpressionStatement
  override def leaveExpressionStatement(expressionStatement: ExpressionStatement): Node = {
    leaveDefault(expressionStatement)
  }

  // Callback for entering a BlockStatement
  override def enterBlockStatement(blockStatement: BlockStatement): Boolean = {
    enterDefault(blockStatement)
  }

  // Callback for leaving a BlockStatement
  override def leaveBlockStatement(blockStatement: BlockStatement): Node = {
    leaveDefault(blockStatement)
  }

  // Callback for entering a ForNode
  override def enterForNode(forNode: ForNode): Boolean = {
    enterDefault(forNode)
  }

  // Callback for leaving a ForNode
  override def leaveForNode(forNode: ForNode): Node = {
    leaveDefault(forNode)
  }

  // Callback for entering a FunctionNode
  override def enterFunctionNode(functionNode: FunctionNode): Boolean = {
    enterDefault(functionNode)
  }

  // Callback for leaving a FunctionNode
  override def leaveFunctionNode(functionNode: FunctionNode): Node = {
    leaveDefault(functionNode)
  }

  // Callback for entering a {@link GetSplitState}.
  override def enterGetSplitState(getSplitState: GetSplitState): Boolean = {
    enterDefault(getSplitState)
  }

  // Callback for leaving a {@link GetSplitState}.
  override def leaveGetSplitState(getSplitState: GetSplitState): Node = {
    leaveDefault(getSplitState)
  }

  // Callback for entering an IdentNode
  override def enterIdentNode(identNode: IdentNode): Boolean = {
    enterDefault(identNode)
  }

  // Callback for leaving an IdentNode
  override def leaveIdentNode(identNode: IdentNode): Node = {
    leaveDefault(identNode)
  }

  // Callback for entering an IfNode
  override def enterIfNode(ifNode: IfNode): Boolean = {
    enterDefault(ifNode)
  }

  // Callback for leaving an IfNode
  override def leaveIfNode(ifNode: IfNode): Node = {
    leaveDefault(ifNode)
  }

  // Callback for entering an IndexNode
  override def enterIndexNode(indexNode: IndexNode): Boolean = {
    enterDefault(indexNode)
  }

  // Callback for leaving an IndexNode
  override def leaveIndexNode(indexNode: IndexNode): Node = {
    leaveDefault(indexNode)
  }

  // Callback for entering a JumpToInlinedFinally
  override def enterJumpToInlinedFinally(jumpToInlinedFinally: JumpToInlinedFinally): Boolean = {
    enterDefault(jumpToInlinedFinally)
  }

  // Callback for leaving a JumpToInlinedFinally
  override def leaveJumpToInlinedFinally(jumpToInlinedFinally: JumpToInlinedFinally): Node = {
    leaveDefault(jumpToInlinedFinally)
  }

  // Callback for entering a LabelNode
  override def enterLabelNode(labelNode: LabelNode): Boolean = {
    enterDefault(labelNode)
  }

  // Callback for leaving a LabelNode
  override def leaveLabelNode(labelNode: LabelNode): Node = {
    leaveDefault(labelNode)
  }

  // Callback for entering a LiteralNode
  override def enterLiteralNode(literalNode: LiteralNode[_]): Boolean = {
    enterDefault(literalNode)
  }

  // Callback for leaving a LiteralNode
  override def leaveLiteralNode(literalNode: LiteralNode[_]): Node = {
    leaveDefault(literalNode)
  }

  // Callback for entering an ObjectNode
  override def enterObjectNode(objectNode: ObjectNode): Boolean = {
    enterDefault(objectNode)
  }

  // Callback for leaving an ObjectNode
  override def leaveObjectNode(objectNode: ObjectNode): Node = {
    leaveDefault(objectNode)
  }

  // Callback for entering a PropertyNode
  override def enterPropertyNode(propertyNode: PropertyNode): Boolean = {
    enterDefault(propertyNode)
  }

  // Callback for leaving a PropertyNode
  override def leavePropertyNode(propertyNode: PropertyNode): Node = {
    leaveDefault(propertyNode)
  }

  // Callback for entering a ReturnNode
  override def enterReturnNode(returnNode: ReturnNode): Boolean = {
    enterDefault(returnNode)
  }
  // Callback for leaving a ReturnNode
  override def leaveReturnNode(returnNode: ReturnNode): Node = {
    leaveDefault(returnNode)
  }
  // Callback for entering a RuntimeNode
  override def enterRuntimeNode(runtimeNode: RuntimeNode): Boolean = {
    enterDefault(runtimeNode)
  }

  // Callback for leaving a RuntimeNode
  override def leaveRuntimeNode(runtimeNode: RuntimeNode): Node = {
    leaveDefault(runtimeNode)
  }

  // Callback for entering a {@link SetSplitState}.
  override def enterSetSplitState(setSplitState: SetSplitState): Boolean = {
    enterDefault(setSplitState)
  }

  // Callback for leaving a {@link SetSplitState}.
  override def leaveSetSplitState(setSplitState: SetSplitState): Node = {
    leaveDefault(setSplitState)
  }

  // Callback for entering a SplitNode
  override def enterSplitNode(splitNode: SplitNode): Boolean = {
    enterDefault(splitNode)
  }

  // Callback for leaving a SplitNode
  override def leaveSplitNode(splitNode: SplitNode): Node = {
    leaveDefault(splitNode)
  }

  // Callback for entering a SplitReturn
  override def enterSplitReturn(splitReturn: SplitReturn): Boolean = {
    enterDefault(splitReturn)
  }

  // Callback for leaving a SplitReturn
  override def leaveSplitReturn(splitReturn: SplitReturn): Node = {
    leaveDefault(splitReturn)
  }

  // Callback for entering a SwitchNode
  override def enterSwitchNode(switchNode: SwitchNode): Boolean = {
    enterDefault(switchNode)
  }

  // Callback for leaving a SwitchNode
  override def leaveSwitchNode(switchNode: SwitchNode): Node = {
    leaveDefault(switchNode)
  }

  // Callback for entering a TernaryNode
  override def enterTernaryNode(ternaryNode: TernaryNode): Boolean = {
    enterDefault(ternaryNode)
  }

  // Callback for leaving a TernaryNode
  override def leaveTernaryNode(ternaryNode: TernaryNode): Node = {
    leaveDefault(ternaryNode)
  }

  // Callback for entering a ThrowNode
  override def enterThrowNode(throwNode: ThrowNode): Boolean = {
    enterDefault(throwNode)
  }

  // Callback for leaving a ThrowNode
  override def leaveThrowNode(throwNode: ThrowNode): Node = {
    leaveDefault(throwNode)
  }

  // Callback for entering a TryNode
  override def enterTryNode(tryNode: TryNode): Boolean = {
    enterDefault(tryNode)
  }

  // Callback for leaving a TryNode
  override def leaveTryNode(tryNode: TryNode): Node = {
    leaveDefault(tryNode)
  }

  // Callback for entering a {@link JoinPredecessorExpression}.
  override def enterJoinPredecessorExpression(expr: JoinPredecessorExpression): Boolean = {
    enterDefault(expr)
  }

  // Callback for leaving a {@link JoinPredecessorExpression}.
  override def leaveJoinPredecessorExpression(expr: JoinPredecessorExpression): Node = {
    leaveDefault(expr)
  }

  // Callback for entering a VarNode
  override def enterVarNode(varNode: VarNode): Boolean = {
    enterDefault(varNode)
  }

  // Callback for leaving a VarNode
  override def leaveVarNode(varNode: VarNode): Node = {
    leaveDefault(varNode)
  }

  // Callback for entering a WhileNode
  override def enterWhileNode(whileNode: WhileNode): Boolean = {
    enterDefault(whileNode)
  }

  // Callback for leaving a WhileNode
  override def leaveWhileNode(whileNode: WhileNode): Node = {
    leaveDefault(whileNode)
  }

  // Callback for entering a WithNode
  override def enterWithNode(withNode: WithNode): Boolean = {
    enterDefault(withNode)
  }

  // Callback for leaving a WithNode
  override def leaveWithNode(withNode: WithNode): Node = {
    leaveDefault(withNode)
  }
}
