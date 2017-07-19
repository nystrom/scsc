package scsc.core

trait SCConfigs {
  // Terms are the configurations on which the supercompiler runs.
  type Config <: AnyRef

  // Extra information returned by the driver/splitter
  // to help residualization.
  // Stored on edges of the graph.
  trait EdgeKind
  case object Drive extends EdgeKind
  // Remember that we split here.
  // Strictly we don't need to store the config and position since they're in the parent node.
  import Graphs.SPath
  case class SplitAt(config: Config, pos: SPath, index: Int, arity: Int) extends EdgeKind
}

trait SCGraphs extends SCConfigs {
  import Graphs._
  type Graph = SGraph[Config, EdgeKind]
  type Node = SNode[Config, EdgeKind]
  type Edge = SEdge[Config, EdgeKind]

  def inject(c: Config): Graph = {
    SGraph[Config, EdgeKind](SNode(c, None, None, Nil)::Nil, Nil, Nil)
  }

  type Pos = SPath

  trait Context {
    // Return the configuration of the current node
    def currentConfig: Option[Config]

    // Return the position of the current node
    def currentPos: Option[Pos]

    // Return the configurations on the path from the current node to the root.
    // Returns Nil if the graph is complete.
    def configPath: List[Config] = currentPath.map(_._2)
    def currentPath: List[(Pos, Config, Option[EdgeKind])]

    def pathFrom(pos: Pos): List[(Pos, Config, Option[EdgeKind])]

    def pathToSplit(pos: Pos): (List[(Pos, Config)], Int, Int) = {
      pathFrom(pos).span {
        case (pos, config, Some(SplitAt(_, _, _, _))) => false
        case (pos, config, _) => true
      } match {
        case (beforeSplit, (pos, config, Some(SplitAt(splitConfig, splitPos, i, n)))::_) =>
          val path = beforeSplit map {
            case (pos, config, _) => (pos, config)
          }
          (path :+ (pos, config) :+ (splitPos, splitConfig), i, n)
        case _ =>
          (Nil, 0, 0)
      }
    }

    // Return the configuration at the given position
    def configAt(pos: Pos): Option[Config]

    def isComplete: Boolean

    def complete: List[(Pos, Config)]
  }

  class GraphContext(private val g: Graph) extends Context {
    // Return the current configuration
    def currentConfig: Option[Config] = g.current.map(_.config)

    def currentPos: Option[Pos] = g.current.map(_.path)

    // Return the configurations on the path from the current node to the root.
    // Returns Nil if the graph is complete.
    def currentPath: List[(Pos, Config, Option[EdgeKind])] = {
      g match {
        case SGraph(n::incomplete, leaves, complete) => pathFrom(n)
        case SGraph(Nil, leaves, complete) => Nil
      }
    }

    def pathFrom(pos: Pos): List[(Pos, Config, Option[EdgeKind])] = g match {
      case SGraph(incomplete, _, complete) =>
        val start: Option[Node] = (incomplete ++ complete).find(_.path == pos)
        start match {
          case None => Nil
          case Some(start) => pathFrom(start)
        }
    }

    private def pathFrom(n: Node): List[(Pos, Config, Option[EdgeKind])] = n match {
      case SNode(config, Some(SEdge(parent, info)), _, pos) => (pos, config, Some(info)) :: pathFrom(parent)
      case SNode(config, None, _, pos) => (pos, config, None) :: Nil
    }

    def configAt(pos: Pos) = g match {
      case SGraph(incomplete, _, complete) =>
        (incomplete.find(_.path == pos) ++ complete.find(_.path == pos)).collectFirst { case n => n.config }
    }

    def isComplete: Boolean = g match {
      case SGraph(Nil, leaves, complete) => true
      case _ => false
    }

    def complete: List[(Pos, Config)] = g match {
      case SGraph(_, _, complete) => complete.map { n => (n.path, n.config) }
    }
  }

}

// The basic supercompilation logic.
trait SC extends SCConfigs with SCGraphs with Whistles {
  def supercompile(c: Config): List[Config] = {
    // create the initial graph
    val g = inject(c)
    val gs = scGraph(g)
    for {
      g <- gs
      n <- g.completeNodes
    } yield n.config
  }

  // Simple whistle using HE.
  def whistle: Whistle = DepthWhistle(1000) | (MightDivergeWhistle() & HEWhistle())

  // Take a step.
  def step(c: Config)(implicit context: Context): List[(Config, EdgeKind)]

  // List of rebuild configurations for the given config.
  def rebuilds(c: Config)(implicit context: Context): List[Config]

  // List of rollback configurations for the given config.
  def rollbacks(c: Config)(implicit context: Context): List[(Pos, Config)]

  // Split the configuration, returning information to rebuild.
  def split(c: Config)(implicit context: Context): List[(Config, EdgeKind)]

  // Rebuild a split configuration (FIXME: hoist this here and perform on the graph)
  // def unsplit(context: Context): List[(Pos, Config)]

  // Is the configuration a final configuration?
  def halts(c: Config)(implicit context: Context): Boolean

  def generalize(c1: Config, c2: Config)(implicit context: Context): Option[Config]

  // Rebuild after a split
  def unsplit(rootConfig: Config, splitConfigs: List[(Pos, Config)])(implicit context: Context): List[Config]


  // Naively discard all but the first graph generated during
  // supercompilation. A better implementation would choose the
  // graph of least cost from all the possibilities.
  def pruneGraphs(gs: List[Graph]) = gs.headOption.toList

  private def scGraph(g: Graph): List[Graph] = {
    println(s"SC ${g.current}")

    var worklist = g::Nil

    while (worklist.nonEmpty) {
      worklist match {
        case g::_ if g.isComplete =>
          println(s"COMPLETE $g")
          return g::Nil

        case g::gs =>
          worklist = gs

          fold(g) match {
            case None =>
              // We didn't fold.
              if (whistle.whistle(g)) {
                // The whistle blew.
                // Try rebuilding.
                println(s"WHISTLE ${g.current}")
                worklist ++= pruneGraphs(rebuild(g) ++ rollback(g))
              }
              else {
                // Try driving, splitting, and rebuilding.
                worklist ++= pruneGraphs(drive(g) ++ split(g) ++ rebuild(g) ++ rollback(g))
              }
            case Some(g1) =>
              // we folded
              println(s"FOLDED ${g.current} -> ${g1.current}")
              worklist = g1::worklist
          }

        case Nil =>
          return Nil
      }
    }

    Nil
  }

  private def fold(g: Graph): Option[Graph] = {
    g.current match {
      case Some(n) =>
        val nn = normalize(n.config)
        g.completeNodes find {
          n1 => isInstance(nn, normalize(n1.config))
        } map {
          n1 => g.fold(n1.path)
        }
      case None =>
        None
    }
  }

  // The difficult part of implementing a supercompiler
  // is the residualization. Rebuilding the program from the graph
  // of configurations.
  // We approach the problem as follows.
  // We introduce residual values.
  // To recreate a term from a graph.

  // If a state cannot take a step, we replace it with
  // the stuck state.

  private def drive(g: Graph): List[Graph] = {
    g.current.toList flatMap {
      case n if halts(n.config)(new GraphContext(g)) =>
        println(s"HALTED ${n.config}")
        g.complete::Nil
      case n =>
        println(s"STEPPING ${n.config}")
        step(n.config)(new GraphContext(g)) match {
          case Nil =>
            Nil
          case configs =>
            println(s"STEPPED TO $configs")
            // We stepped to one or more configurations.
            // Return all the possible graphs.
            configs map {
              case (config, info) => g.addChild(config, info)
            }
        }
    }
  }

  private def split(g: Graph): List[Graph] = {
    g.current.toList flatMap {
      case n =>
        // Cannot take a step and it's not a Halt configuration
        // Split into multiple configurations
        val configs = split(n.config)(new GraphContext(g))
        // FIXME: split should return the merge function
        configs match {
          case Nil =>
            Nil
          case configs =>
            // split successful
            // Add the nodes to the same graph.
            g.addChildren(configs)::Nil
        }
    }
  }

  def unsplit(g: Graph): List[(Pos, Config)] = {
    import Graphs._
    val context = new GraphContext(g)

    val hs = g.completeLeaves.map {
      case SNode(st, _, _, pos) => (pos, st)
    }
    val hpaths = hs map { case (pos, st) => (pos, st, context.pathFrom(pos)) }
    val splitPaths: List[(Pos, Config, Pos, Config, Int, Int)] = hpaths flatMap {
      case (pos, st, path) =>
        path.collectFirst {
          case (_, _, Some(SplitAt(s0, pos0, i, n))) => (pos, st, pos0, s0, i, n)
        }.toList
    }

    val grouped: Map[Pos, List[(Pos, Config, Pos, Config, Int, Int)]] = splitPaths.groupBy(_._3)

    val complete = grouped.collect {
      case (pos0, paths @ (p::_)) if p._6 == paths.length => paths.sortBy(_._5)
    }.toList

    println(s"UNSPLIT $complete")

    complete flatMap {
      case paths =>
        val inputs = paths map { p => (p._1, p._2) }
        paths match {
          case (pos, st, pos0, s0, i, n)::_ =>
            unsplit(s0, inputs)(context) map {
              s => (pos0, s)
            }
          case Nil =>
            Nil
        }
    }
  }

  private def rebuild(g: Graph): List[Graph] = {
    g.current.toList flatMap {
      case n =>
        rebuilds(n.config)(new GraphContext(g)) map {
          case c => g.rebuild(c)
        }
    }
  }

  private def rollback(g: Graph): List[Graph] = {
    // TODO
    // find all complete nodes with a split ancestor of the right arity
    // then pass the ancestor and the complete nodes to back to JS
    g.current.toList flatMap {
      case n =>
        val rbs = rollbacks(n.config)(new GraphContext(g)) map {
          case (path, c) =>
            g.rollback(path, c)
        }
        val folds: List[Graph] = n.foldWith.toList flatMap {
          path =>
            g.completeNodes.find(_.path == path) match {
              case Some(n1) =>
                generalize(n.config, n1.config)(new GraphContext(g)) match {
                  case Some(c) =>
                    g.rollback(path, c)::Nil
                  case None =>
                    Nil
                }
              case None =>
                Nil
            }
        }
        rbs ++ folds
    }
  }
}
