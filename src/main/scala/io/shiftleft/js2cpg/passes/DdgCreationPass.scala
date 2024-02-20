package io.shiftleft.js2cpg.passes

import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.{EdgeTypes, Operators}
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.js2cpg.core.Report
import io.shiftleft.js2cpg.utils.SourceWrapper.*
import io.shiftleft.passes.ConcurrentWriterCpgPass
import io.shiftleft.semanticcpg.language.*
import org.slf4j.LoggerFactory

import scala.collection.mutable
import scala.util.{Failure, Success, Try}

/**
 * Given a populated CPG, this pass creates the data dependence graph (DDG) for each method.
 * Methods are processed in parallel.
 */
class DdgCreationPass(cpg: Cpg, report: Report)
    extends ConcurrentWriterCpgPass[Method](cpg) {

  private case class PseudoIdentifier(name: String, position: Int)

  private type DDGCalcSet = Set[(PseudoIdentifier, Long)]

  private val logger = LoggerFactory.getLogger(getClass)

  override def generateParts(): Array[Method] = cpg.method.toArray

  override def runOnPart(diffGraph: DiffGraphBuilder, part: Method): Unit = {
    val result = createDdg(part)
    result match {
      case Failure(exception) =>
        logger.warn(s"Failed to generate DDG for method '${part.name}'!", exception)
      case Success(localDiff) =>
        logger.info(s"Processed DDG for method '${part.name}'")
        diffGraph.absorb(localDiff)
    }
  }

  /**
   * Create DDG for given method.
   *
   * Implemented by Simon Koch and Malte Wessels.
   *
   * @param method method to analyze
   * @return populated diffGraph
   */
  private def createDdg(method: Method): Try[DiffGraphBuilder] = {
    implicit val localDiff: DiffGraphBuilder = new DiffGraphBuilder
    Try {
      // here we get all the cfg nodes in depth first spanning tree order which is supposed to optimize runtime
      val cfgNodes = generateDepthFirstSpanningTreeOrder(method)
      // here we generate the initial out set and the final gen, and kill sets for each cfg node
      val (gen, out, kill) = genOutKillPreparation(cfgNodes)
      // here we calculate the final in and out set for each cfg node
      val in = inOutSetCalculation(cfgNodes, out, gen, kill)
      // here we create the reaching definition edges based on the in set finalized before
      createReachingEdge(in)
      localDiff
    }
  }

  /**
   * Returns all cfg nodes of a method in depth first spanning tree order
   *
   * Algorithm based on Compiler Bau II by Alfred V. Aho, Ravi Sethis, and Jeffrey D. Ullmann
   * Chapter 10.9, Algorithm 10.14
   *
   * Implemented by Simon Koch and Malte Wessels.
   *
   * @param start the start of the cfg i.e., the method itself
   * @return list of all contained cfg nodes in depth first spanning tree order
   */
  private def generateDepthFirstSpanningTreeOrder(start: Method): List[CfgNode] = {
    val order: collection.mutable.ListBuffer[(Int, CfgNode)] =
      collection.mutable.ListBuffer()
    val cfgNodeCount = start.ast.isCfgNode.l.length

    def populateOrder(current: CfgNode, i: Int, recursionDepth: Int = 0)(
      implicit visited: collection.mutable.Set[CfgNode]): Int = {
      assert(
        recursionDepth <= cfgNodeCount,
        s"the recursion depth exceeded the maximum amount of cfg nodes of $cfgNodeCount")
      var currentI = i
      current._cfgOut.foreach { next =>
        if (!visited.contains(next.asInstanceOf[CfgNode])) {
          visited.addOne(next.asInstanceOf[CfgNode])
          currentI = populateOrder(next.asInstanceOf[CfgNode],
            currentI,
            recursionDepth + 1)
        }
      }
      order.append((currentI, current))
      currentI - 1
    }

    populateOrder(start, cfgNodeCount)(collection.mutable.Set())
    order.sortBy(_._1).map(_._2).toList
  }

  /**
   * Prepare the sets for out gen and kill for each cfg node
   *
   * This is done by checking whether the given cfg node is a known writing call and if so
   * gen and kill are set to Set((Identifier, call))
   *
   * Implemented by Simon Koch and Malte Wessels.
   *
   * @param cfgNodes all the cfg nodes of a given method
   * @return gen, out and kill maps
   */
  private def genOutKillPreparation(cfgNodes: List[CfgNode]): (Map[CfgNode, DDGCalcSet],
                                                               Map[CfgNode, DDGCalcSet],
                                                               Map[CfgNode, DDGCalcSet]) = {
    var gen: Map[CfgNode, DDGCalcSet] = Map()
    var out: Map[CfgNode, DDGCalcSet] = Map()
    var kill: Map[CfgNode, DDGCalcSet] = Map()

    cfgNodes.foreach {
      case call: Call =>
        WriteOps.writes.find(_.operation == call.name) match {
          case Some(WriteOps.IdentifierWrite(_, position, _)) =>

            val tmpChildAtPos =
              call.astChildren
                .order(position)
                .head

            // Either the Identifier is directly under the writing Call at the given position
            // or there is a field access first.
            // In latter case, we only consider the Identifiers as a whole.
            val identifier: PseudoIdentifier = tmpChildAtPos match {
              case i : Identifier => PseudoIdentifier(i.name, i.order)
              case c: Call if c.name == Operators.fieldAccess =>
                val tmpIdentifier = c.astChildren.order(1).head.asInstanceOf[Identifier]
                PseudoIdentifier(tmpIdentifier.name, tmpIdentifier.order)
            }


            val newElement: DDGCalcSet = Set((identifier, call.id()))

            gen = gen + (call -> (gen.getOrElse(call, Set()) ++ newElement))
            out = out + (call -> (out.getOrElse(call, Set()) ++ newElement))
            kill = kill + (call -> (kill.getOrElse(call, Set()) ++ newElement))
          case _ =>
            gen = gen + (call -> Set())
            out = out + (call -> Set())
            kill = kill + (call -> Set())
        }
      case method: Method =>
        logger.warn("found method " + method.name)
        method.astOut.isParameter.foreach(param => {
          val identifier = PseudoIdentifier(param.name, param.order)
          val newElement: DDGCalcSet = Set((identifier, method.id()))

          gen = gen + (method -> (gen.getOrElse(method, Set()) ++ newElement))
          out = out + (method -> (out.getOrElse(method, Set()) ++ newElement))
          kill = kill + (method -> (kill.getOrElse(method, Set()) ++ newElement))
        })
      case node: CfgNode =>
        gen = gen + (node -> Set())
        out = out + (node -> Set())
        kill = kill + (node -> Set())
    }
    (gen, out, kill)
  }

  /**
   * Algorithm based on Compiler Bau II by Alfred V. Aho, Ravi Sethis, and Jeffrey D. Ullmann
   * Chapter 10.6 Algorithm 10.2
   *
   * Implemented by Simon Koch and Malte Wessels.
   *
   * @param cfgNodes all the cfg nodes of a given method
   * @param gen      the gen set for each cfgNode to be worked with
   * @param out      the out set for each cfgNode to be generated/worked on
   * @param kill     the kill set for each cfgNode to be worked with
   */
  private def inOutSetCalculation(cfgNodes: List[CfgNode], gen: Map[CfgNode, DDGCalcSet], out: Map[CfgNode, DDGCalcSet],
                                  kill: Map[CfgNode, DDGCalcSet]): Map[CfgNode, DDGCalcSet] = {

    var currentIn: Map[CfgNode, DDGCalcSet] = Map()
    var currentOut = out
    var change: Boolean = true

    while (change) {
      change = false
      cfgNodes.foreach { node =>

        // Get mutable calc set for all preceding nodes.
        val mInUnionSet: mutable.HashSet[(PseudoIdentifier, Long)] = new mutable.HashSet[(PseudoIdentifier, Long)]
        for (pre <- node.cfgIn.map(x => x.asInstanceOf[CfgNode])) {
          mInUnionSet ++= currentOut(pre)
        }

        // Add this set to the currentIn map.
        currentIn = currentIn + (node -> mInUnionSet.toSet)

        val oldOut = currentOut(node)

        val killedVariableList = kill(node).toList
        var newOut = Set[(PseudoIdentifier, Long)]()
        // if there is no variable killed
        if (killedVariableList.isEmpty) {
          // then all incoming variables plus the generated variables are outgoing
          newOut = gen(node) union currentIn(node)
        } else {
          // if stuff is killed then we have to filter the incoming set for those variables before
          // creating the union with the generated variables
          newOut = gen(node) union currentIn(node).filter(c => !killedVariableList.exists(k => k._1.name == c._1.name))
        }

        if ((newOut &~ oldOut).nonEmpty) {
          change = true
          currentOut = currentOut + (node -> newOut)
        }

        // after updating the set for the call is either the same or larger
        assert(currentOut(node).size >= oldOut.size)
        // the size has to be the size of the newOut as it is either the same or has been larger
        assert(currentOut(node).size == newOut.size)
      }
    }
    currentIn
  }

  /**
   * Based on a calculated in set create corresponding reaching edges
   *
   * Implemented by Simon Koch and Malte Wessels.
   *
   * @param in        a map giving you the incoming identifier,definingCall pairs for a given call
   * @param diffGraph the diffGraph to generate which is later merged into a preexisting cpg
   */
  private def createReachingEdge(in: Map[CfgNode, DDGCalcSet])(implicit diffGraph: DiffGraphBuilder): Unit = {
    in.filter(_._1.isInstanceOf[Call]).foreach {
      case (callNode, set) =>
        val call: Call = callNode.asInstanceOf[Call]
        // these are the identifiers used in the current expression
        val usedIdentifiers = getUsedIdentifiers(call)
        // these are the identifiers used in the current expression intersected with the incoming identifiers
        val inIntersection = usedIdentifiers.filter(ident => set.exists(elem => elem._1.name == ident.name))
        // this is the write op the current callNode corresponds with
        val writeOp = WriteOps.writes.find(_.operation == callNode.asInstanceOf[Call].name)
        // now we go over the intersecting identifier
        inIntersection.foreach { identifier =>
          // and based on whether we have a write op we create reaching edges
          writeOp match {
            // if it is a write op call we have to check that it is either a reading write op or the identifier
            // is not at the writing position
            case Some(WriteOps.IdentifierWrite(_, position, reading)) =>
              if (reading || identifier.position != position) {
                linkDefinitions(set, callNode, identifier)
              }
            // if it is not a write op we can simply add the edge
            case None =>
              linkDefinitions(set, callNode, identifier)
          }
        }
    }
  }

  /**
   * Get used Identifier in the current Call.
   *
   * Implemented by Simon Koch and Malte Wessels.
   *
   * @param call current Call
   * @return used Identifier in the current Call
   */
  private def getUsedIdentifiers(call: Call): Set[PseudoIdentifier] = {
    val set: mutable.HashSet[Identifier] = new mutable.HashSet[Identifier]
    // Buffer in Identifier Set to prevent duplicates
    call.astMinusRoot.isIdentifier
      .filter(x => x.astIn.nonEmpty && x.astIn.head.isInstanceOf[Call])
      // Only add if Identifier with same variable name does not yet exist
      .foreach(x => if (!set.exists(i => i.name == x.name)) set.addOne(x))
    // Then create PseudoIdentifier Set
    set.map(x => PseudoIdentifier(x.name, x.order)).toSet
  }

  /**
   * Link each Definition to the corresponding Identifier.
   *
   * @param set        generated calc set
   * @param callNode   current call node
   * @param identifier current identifier
   */
  private def linkDefinitions(set: DDGCalcSet, callNode: CfgNode, identifier: PseudoIdentifier)
                             (implicit diffGraph: DiffGraphBuilder): Unit = {
    val definitions =
      set.filter(elem => elem._1.name == identifier.name)
    definitions.foreach {
      case (identifier, definedAt) =>
        addReachingEdge(
          cpg.all.id(definedAt).head.asInstanceOf[CfgNode],
          callNode,
          identifier.name)
    }
  }

  /**
   * Draw a REACHING_DEF edge between two nodes.
   *
   * @param fromNode   node from which the edge is going
   * @param toNode     node to which the edge is going
   * @param identifier concerning identifier, currently not represented in the edge properties
   * @param diffGraph  the graph the edge is added to
   */
  private def addReachingEdge(fromNode: CfgNode, toNode: CfgNode, identifier: String)
                             (implicit diffGraph: DiffGraphBuilder): Unit = {
    try {
      diffGraph.addEdge(fromNode, toNode, EdgeTypes.REACHING_DEF)
    } catch
      case _ =>
        logger.warn(s"Creating CFG edge failed between '${fromNode.code}' and '${toNode.code}'")
  }

}
