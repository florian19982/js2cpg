package io.shiftleft.js2cpg.passes

import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.EdgeTypes
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.js2cpg.core.Report
import io.shiftleft.js2cpg.utils.SourceWrapper.*
import io.shiftleft.passes.ConcurrentWriterCpgPass
import io.shiftleft.semanticcpg.language.*
import org.slf4j.LoggerFactory

import scala.util.{Failure, Success, Try}

/**
 * Given a populated CPG, this pass creates the data dependence graph (DDG) for each method.
 * Methods are processed in parallel.
 */
class DdgCreationPass(cpg: Cpg, report: Report)
    extends ConcurrentWriterCpgPass[Method](cpg) {

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
   * @param method method for DDG creation
   */
  private def createDdg(method: Method): Try[DiffGraphBuilder] = {
    implicit val localDiff: DiffGraphBuilder = new DiffGraphBuilder
    Try {
      // Do stuff here
      localDiff
    }
  }

  /**
   * Draw a REACHING_DEF edge between two nodes.
   *
   * @param fromNode   node from which the edge is going
   * @param toNode     node to which the edge is going
   * @param identifier concerning identifier
   * @param diffGraph  the graph the edge is added to
   */
  private def addReachingEdge(fromNode: CfgNode, toNode: CfgNode, identifier: String)
                             (implicit diffGraph: DiffGraphBuilder): Unit = {
    try {
      diffGraph.addEdge(fromNode, toNode, EdgeTypes.REACHING_DEF, List(("VARIABLE", identifier)))
    } catch
      case _ =>
        logger.warn(s"Creating CFG edge failed between '${fromNode.code}' and '${toNode.code}'")
  }

}
