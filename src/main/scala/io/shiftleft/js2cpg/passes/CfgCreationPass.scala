package io.shiftleft.js2cpg.passes

import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.{ControlStructureTypes, EdgeTypes}
import io.shiftleft.codepropertygraph.generated.nodes.{AstNode, Block, Call, ControlStructure, Local, Method, MethodReturn}
import io.shiftleft.js2cpg.core.Report
import io.shiftleft.js2cpg.utils.SourceWrapper.*
import io.shiftleft.passes.ConcurrentWriterCpgPass
import io.shiftleft.semanticcpg.language.*
import org.slf4j.LoggerFactory

import scala.collection.mutable.ListBuffer
import scala.util.{Failure, Success, Try}

/**
 * Given a populated CPG, this pass creates the control flow graph (CFG) for each method.
 * Methods are processed in parallel.
 */
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
      case astNode: Call =>
        handleCfgCall(astNode, lastNodes)
      case astNode: ControlStructure =>
        handleCfgControlStructure(astNode, lastNodes)
      case _ =>
        handleCfgGeneric(astNode, lastNodes)
    }
  }

  private def handleCfgControlStructure(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                       (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    controlStructure.controlStructureType match {
      case ControlStructureTypes.IF =>
        handleCfgControlStructureIf(controlStructure, lastNodes)
      case ControlStructureTypes.WHILE =>
        handleCfgControlStructureWhile(controlStructure, lastNodes)
      case _ =>
        logger.warn(s"unhandled control structure type '${controlStructure.controlStructureType}'.")
        lastNodes
    }
  }

  private def handleCfgControlStructureIf(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                         (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    // Link condition node to lastNodes
    val conditionNodeList: List[AstNode] = createConditionNodeList(controlStructure, lastNodes)
    // Now add if and else Nodes and connect them to the condition node
    val ifNodeList: List[AstNode] = createTrueNodeList(controlStructure, conditionNodeList)
    val elseNodeList: List[AstNode] = createFalseNodeList(controlStructure, conditionNodeList)
    (new ListBuffer[AstNode] ++= ifNodeList ++= elseNodeList).toList
  }

  private def handleCfgControlStructureWhile(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                            (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    val conditionNodeList: List[AstNode] = createConditionNodeList(controlStructure, lastNodes)
    val whileNodeList: List[AstNode] = createTrueNodeList(controlStructure, conditionNodeList)
    // After the execution block of the while return to the first parameter of the condition. (TRUE-Edge)
    // From there the loop starts again.
    for (whileNode <- whileNodeList) {
      addCfgEdge(whileNode, conditionNodeList.head.astChildren.head)
    }
    // The condition node list is returned.
    // Therefore, in the next step it is connected to the rest of the program
    // in case the condition does not hold (FALSE-Edge)
    conditionNodeList
  }

  private def createConditionNodeList(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                     (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    // Link condition node to lastNodes
    createCfgStep(controlStructure.astChildren.filter(_.order == 1).head, lastNodes)
  }

  private def createTrueNodeList(controlStructure: ControlStructure, conditionNodeList: List[AstNode])
                                (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    var trueNodeList: List[AstNode] = conditionNodeList
    if (controlStructure.astChildren.exists(_.order == 2)) {
      // TRUE Edges
      trueNodeList = createCfgStep(controlStructure.astChildren.filter(_.order == 2).head, conditionNodeList)
    }
    trueNodeList
  }

  private def createFalseNodeList(controlStructure: ControlStructure, conditionNodeList: List[AstNode])
                                 (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    var falseNodeList: List[AstNode] = conditionNodeList
    if (controlStructure.astChildren.exists(_.order == 3)) {
      // FALSE Edges
      falseNodeList = createCfgStep(controlStructure.astChildren.filter(_.order == 3).head, conditionNodeList)
    }
    falseNodeList
  }

  private def handleCfgCall(call: Call, lastNodes: List[AstNode])
                              (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    var localLastNodes: List[AstNode] = lastNodes
    if (call.astChildren.toArray.isEmpty) {
      localLastNodes = handleCfgNoChildren(call, localLastNodes)
    } else {
      // Catch special calls here
      localLastNodes = handleCfgGeneric(call, lastNodes)
    }
    addEdgesForAllLastNodes(call, localLastNodes)
    new ListBuffer[AstNode].addOne(call).toList
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
