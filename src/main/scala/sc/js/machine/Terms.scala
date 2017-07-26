package sc.js.machine

trait Terms extends sc.imp.machine.Terms with sc.js.syntax.Trees {
  this: Stores =>

  val Parser: Parser[this.type]
  val TreeWalk: TreeWalk[this.type]
}
