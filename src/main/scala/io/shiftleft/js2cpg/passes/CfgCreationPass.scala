package io.shiftleft.js2cpg.passes

import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.EdgeTypes
import io.shiftleft.codepropertygraph.generated.nodes.{AstNode, Block, Call, Local, Method, MethodReturn}
import io.shiftleft.js2cpg.core.Report
import io.shiftleft.js2cpg.utils.SourceWrapper.*
import io.shiftleft.passes.ConcurrentWriterCpgPass
import io.shiftleft.semanticcpg.language.*
import org.slf4j.LoggerFactory

import scala.collection.mutable.ListBuffer
import scala.util.{Failure, Success, Try}


class CfgCreationPass(cpg: Cpg, report: Report)
    extends ConcurrentWriterCpgPass[Method](cpg) {

  private val logger = LoggerFactory.getLogger(getClass)

  override def generateParts(): Array[Method] = cpg.method.toArray

  override def runOnPart(diffGraph: DiffGraphBuilder, part: Method): Unit = {
    val result = createCfg(part)
    result match {
      case Failure(exception) =>
        logger.warn(s"Failed to generate CFG for method '${part.name}'!", exception)
      case Success(localDiff) =>
        logger.info(s"Processed CFG for method '${part.name}'")
        diffGraph.absorb(localDiff)
    }
  }

  private def createCfg(method: Method): Try[DiffGraphBuilder] = {
    implicit val localDiff: DiffGraphBuilder = new DiffGraphBuilder
    Try {
      var localLastNodes: List[AstNode] = new ListBuffer[AstNode].addOne(method).toList
      for (child <- method.astChildren.sortBy(_.order) if child.isInstanceOf[Block]
        || child.isInstanceOf[MethodReturn]) {
        localLastNodes = createCfgStep(child, localLastNodes)
      }
      localDiff
    }
  }

  private def createCfgStep(astNode: AstNode, lastNodes: List[AstNode])
                           (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    astNode match {
      case _: Method | _: Local =>
        // Ignore.
        lastNodes
      case _: Call =>
        handleCfgCall(astNode, lastNodes)
      case _ =>
        handleCfgGeneric(astNode, lastNodes)
    }
  }

  private def handleCfgCall(astNode: AstNode, lastNodes: List[AstNode])
                              (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    var localLastNodes: List[AstNode] = lastNodes
    if (astNode.astChildren.toArray.isEmpty) {
      localLastNodes = handleCfgNoChildren(astNode, localLastNodes)
    } else {
      // Catch special calls here
      localLastNodes = handleCfgGeneric(astNode, lastNodes)
    }
    addEdgesForAllLastNodes(astNode, localLastNodes)
    new ListBuffer[AstNode].addOne(astNode).toList
  }

  private def handleCfgGeneric(astNode: AstNode, lastNodes: List[AstNode])
                              (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    var localLastNodes: List[AstNode] = lastNodes
    if (astNode.astChildren.toArray.isEmpty) {
      localLastNodes = handleCfgNoChildren(astNode, localLastNodes)
    } else {
      for (child <- astNode.astChildren) {
        localLastNodes = createCfgStep(child, localLastNodes)
      }
    }
    localLastNodes
  }

  private def handleCfgNoChildren(astNode: AstNode, lastNodes: List[AstNode])
                                 (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    addEdgesForAllLastNodes(astNode, lastNodes)
    new ListBuffer[AstNode].addOne(astNode).toList
  }

  private def addEdgesForAllLastNodes(astNode: AstNode, lastNodes: List[AstNode])
                                     (implicit diffGraph: DiffGraphBuilder): Unit = {
    for (lastNode <- lastNodes) {
      addCfgEdge(lastNode, astNode)
    }
  }

  private def addCfgEdge(fromNode: AstNode, toNode: AstNode)(implicit diffGraph: DiffGraphBuilder): Unit = {
    try {
      diffGraph.addEdge(fromNode, toNode, EdgeTypes.CFG)
    } catch
      case _ =>
        logger.warn(s"Creating CFG edge failed between '${fromNode.code}' and '${toNode.code}'")
  }

}
