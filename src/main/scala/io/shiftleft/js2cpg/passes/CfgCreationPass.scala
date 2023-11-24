package io.shiftleft.js2cpg.passes

import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.{ControlStructureTypes, EdgeTypes}
import io.shiftleft.codepropertygraph.generated.nodes.{AstNode, Block, Call, ControlStructure, JumpTarget, Local,
  Method, MethodReturn}
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
  private final val CaseName: String = "case"

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
      case ControlStructureTypes.DO =>
        handleCfgControlStructureDo(controlStructure, lastNodes)
      case ControlStructureTypes.FOR =>
        handleCfgControlStructureFor(controlStructure, lastNodes)
      case ControlStructureTypes.SWITCH =>
        handleCfgControlStructureSwitch(controlStructure, lastNodes)
      case _ =>
        logger.warn(s"unhandled control structure type '${controlStructure.controlStructureType}'.")
        lastNodes
    }
  }

  private def handleCfgControlStructureIf(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                         (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    // Link condition node to lastNodes
    val conditionNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, lastNodes, 1)
    // Now add if and else Nodes and connect them to the condition node
    val ifNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, conditionNodeList, 2)
    val elseNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, conditionNodeList, 3)
    (new ListBuffer[AstNode] ++= ifNodeList ++= elseNodeList).toList
  }

  private def handleCfgControlStructureWhile(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                            (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    val conditionNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, lastNodes, 1)
    val whileNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, conditionNodeList, 2)
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

  private def handleCfgControlStructureDo(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                            (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    val doNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, lastNodes, 1)
    val conditionNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, doNodeList, 2)
    // After the condition block return to the first statement of the do block. (TRUE-Edge)
    // From there the loop starts again.
    for (condNode <- conditionNodeList) {
      addCfgEdge(condNode, doNodeList.head.astChildren.head)
    }
    // The condition node list is returned.
    // Therefore, in the next step it is connected to the rest of the program
    // in case the condition does not hold (FALSE-Edge)
    conditionNodeList
  }

  private def handleCfgControlStructureFor(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                            (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    val conditionNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, lastNodes, 2)
    val forNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, conditionNodeList, 4)
    val postNodeList: List[AstNode] = createNodeListOfOrder(controlStructure, forNodeList, 3)
    // After the execution block of the while return to the first parameter of the condition. (TRUE-Edge)
    // From there the loop starts again.
    for (postNode <- postNodeList) {
      addCfgEdge(postNode, conditionNodeList.head.astChildren.head)
    }
    // The condition node list is returned.
    // Therefore, in the next step it is connected to the rest of the program
    // in case the condition does not hold (FALSE-Edge)
    conditionNodeList
  }

  private def handleCfgControlStructureSwitch(controlStructure: ControlStructure, lastNodes: List[AstNode])
                                             (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    var localLastNodes: List[AstNode] = lastNodes
    if (controlStructure.astChildren.exists(_.order == 1) && controlStructure.astChildren.exists(_.order == 2)) {
      val valueNode = controlStructure.astChildren.filter(_.order == 1).head
      val blockNode = controlStructure.astChildren.filter(_.order == 2).head
      localLastNodes = createCfgStep(valueNode, localLastNodes)
      localLastNodes = createJumpTargetList(valueNode, blockNode)
    }
    localLastNodes
  }

  private def createNodeListOfOrder(controlStructure: ControlStructure, lastNodes: List[AstNode], order: Int)
                                (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    if (controlStructure.astChildren.exists(_.order == order)) {
      // TRUE Edges
      createCfgStep(controlStructure.astChildren.filter(_.order == order).head, lastNodes)
    } else {
      lastNodes
    }
  }

  private def createJumpTargetList(valueNode: AstNode, blockNode: AstNode)
                                  (implicit diffGraph: DiffGraphBuilder): List[AstNode] = {
    val jumpTargetList: ListBuffer[AstNode] = new ListBuffer[AstNode]
    for (jumpTargetNode <- blockNode.astChildren.filter(_.isInstanceOf[JumpTarget]).cast[JumpTarget]) {
      addCfgEdge(valueNode, jumpTargetNode)
      var lastNode: AstNode = jumpTargetNode
      // If it is a When with a compared value (so not WHEN OTHERS), connect this value node to the jump target
      if (jumpTargetNode.name == CaseName && blockNode.astChildren.exists(_.order == lastNode.order + 1)) {
        val checkValueNode = blockNode.astChildren.filter(_.order == lastNode.order + 1).head
        addCfgEdge(jumpTargetNode, checkValueNode)
        lastNode = checkValueNode
      }
      // Find the next executed Call for the current Jump target
      var i: Int = 1
      while (blockNode.astChildren.exists(_.order == lastNode.order + i) &&
        !blockNode.astChildren.filter(_.order == lastNode.order + i).head.isInstanceOf[Call]) {
        i = i + 1
      }
      // Connect to the Value
      if (blockNode.astChildren.exists(_.order == lastNode.order + i) &&
        blockNode.astChildren.filter(_.order == lastNode.order + i).head.isInstanceOf[Call]) {
        val callList: List[AstNode] = createCfgStep(blockNode.astChildren.filter(_.order == lastNode.order + i).head,
          new ListBuffer[AstNode].addOne(lastNode).toList)
        jumpTargetList ++= callList
      }
    }
    jumpTargetList.toList
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
