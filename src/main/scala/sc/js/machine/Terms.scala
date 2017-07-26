package sc.js.machine

trait Terms extends sc.imp.machine.Terms with sc.js.syntax.Trees {
  this: Stores =>

  val Parser: sc.js.syntax.Parser[this.type]
  val TreeWalk: sc.js.syntax.TreeWalk[this.type]
}
