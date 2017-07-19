package scsc.core

// We base our graph representation on the S-graph representation in MRSC.
// Described in Ilya Klyuchnikov and Sergei Romanenko, 2011.
// Graph edges go bottom up from the node to the parent.
// When MRSc drives, it generates a stream of GraphSteps. We avoid this
// and just manipulate the graph directly.
object Graphs {
  type SPath = List[Int]

  sealed trait NEdge {
    def parent: SPath
  }
  case class NSplit(parent: SPath, index: Int, arity: Int) extends NEdge
  case class NDrive(parent: SPath) extends NEdge
  case class NGraph[+C, +D](incomplete: Map[SPath, NNode[C, D]], complete: Map[SPath, NNode[C, D]])
  case class NNode[+C, +D](config: C, parent: Option[NEdge], foldWith: Option[SPath], path: SPath)

  case class SNode[+C, +D](config: C, parent: Option[SEdge[C, D]], foldWith: Option[SPath], path: SPath) {
    override def toString = indent(0)
    def indent(i: Int): String = s"""node
${" " * i}path = ${path.mkString(":")}
${" " * i}foldWith = $foldWith
${" " * i}config = $config
${" " * i}parent = ${parent.map(_.node.indent(i+1)).getOrElse("NONE")}
"""
  }

  case class SEdge[+C, +D](node: SNode[C, D], info: D) {
    override def toString = indent(0)
    def indent(i: Int): String = s"""edge
${" " * i}node = ${node.indent(i+1)}
${" " * i}info = $info
"""
  }

  case class SGraph[+C, +D](incompleteLeaves: List[SNode[C, D]], completeLeaves: List[SNode[C, D]], completeNodes: List[SNode[C, D]]) {
    override def toString = indent(0)
    def indent(i: Int): String = s"""graph
${" " * i}incomplete = ${incompleteLeaves.map(_.indent(i+1)).mkString("\n")}
${" " * i}leaves = ${completeLeaves.map(_.indent(i+1)).mkString("\n")}
${" " * i}complete = ${completeNodes.map(_.indent(i+1)).mkString("\n")}
"""
  }

  implicit class SNodeOps[C, D](n: SNode[C, D]) {
    def ancestors: List[SNode[C, D]] = n match {
      case SNode(_, Some(SEdge(parent, _)), _, _) => parent::parent.ancestors
      case SNode(_, None, _, _) => Nil
    }
  }

  implicit class SGraphOps[C, D](g: SGraph[C, D]) {
    def depth: Int = g match {
      case SGraph(incomplete, leaves, complete) => {
        val lengths = incomplete map {
          case SNode(_, _, _, path) => path.length + 1
        }
        lengths.max
      }
    }

    def size: Int = g match {
      case SGraph(incomplete, leaves, complete) => {
        val lengths = incomplete map {
          case SNode(_, None, _, path) => path.length + 1
        }
        lengths.sum + complete.length
      }
    }

    def isComplete = g match {
      case SGraph(Nil, _, _) => true
      case _ => false
    }

    def current: Option[SNode[C, D]] = g match {
      case SGraph(Nil, _, _) => None
      case SGraph(n::ns, _, _) => Some(n)
    }

    // Mark the current node complete.
    def complete = g match {
      case SGraph(n::incomplete, leaves, complete) =>
        SGraph(incomplete, n::leaves, n::complete)
    }

    def addChild(c: C, d: D) = addChildren((c, d)::Nil)

    // Add children to the current node, completing the node.
    def addChildren(ns: List[(C, D)]) = g match {
      case SGraph((parent @ SNode(config, _, _, path))::incomplete, leaves, complete) =>
        val nodes = ns.zipWithIndex map {
          case ((c, d), i) => SNode[C, D](c, Some(SEdge[C, D](parent, d)), None, i::path)
        }
        nodes match {
          case Nil => SGraph(incomplete, parent::leaves, parent::complete)
          case nodes => SGraph(nodes ++ incomplete, leaves, parent::complete)
        }
    }

    // Map the function over all nodes where root is an ancestor
    def mapSubtree(f: C => C)(root: SPath) = g match {
      case SGraph(incomplete, leaves, complete) =>
        val fnode: SNode[C, D] => SNode[C, D] = {
          case n @ SNode(config, _, _, path) if path.endsWith(root) =>
            n.copy(f(config))
          case n =>
            n
        }
        val incomplete1 = incomplete.map(fnode)
        val leaves1 = leaves.map(fnode)
        val complete1 = complete.map(fnode)
        SGraph(incomplete1, leaves1, complete1)
    }

    // Fold the current node to the node with the given path, completing the node.
    def fold(to: SPath) = g match {
      case SGraph(n::incomplete, leaves, complete) =>
        val n1 = n.copy(foldWith = Some(to))
        SGraph(incomplete, n1::leaves, n1::complete)
    }

    // Rebuild the current node.
    // This updates its configuation, leaving it incomplete.
    def rebuild(c: C) = g match {
      case SGraph(n::incomplete, leaves, complete) =>
        val n1 = n.copy(config = c)
        SGraph(n1::incomplete, leaves, complete)
    }

    // The configuation in the node with the is replaced
    // with the given configuration. The node is added
    // back as a leaf and all descendants of the node
    // are removed from the graph.
    def rollback(to: SPath, c: C) = g match {
      case SGraph(n::incomplete, leaves, complete) =>
        val n1 = n.ancestors.find(_.path == to)
        n1 match {
          case Some(ancestor) =>
            val n2 = ancestor.copy(config = c)
            // Remove all nodes that are descendants of n1
            def prune(n: SNode[C, D]) = n match {
              case SNode(_, _, _, path) => path.endsWith(n2.path)
            }
            val incomplete1 = incomplete.filterNot(prune _)
            val leaves1 = leaves.filterNot(prune _)
            val complete1 = complete.filterNot(prune _)
            SGraph(n2::incomplete1, leaves1, complete1)
          case None =>
            g
        }
    }
  }
}
