package io.shiftleft.js2cpg.passes

import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.EdgeTypes
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.js2cpg.core.Report
import io.shiftleft.js2cpg.utils.SourceWrapper.*
import io.shiftleft.passes.ConcurrentWriterCpgPass
import io.shiftleft.semanticcpg.language.*
import org.slf4j.LoggerFactory

import scala.collection.mutable
import scala.util.{Failure, Success, Try}

/**
 * Given a populated CPG, this pass links call nodes to corresponding method nodes.
 * Calls are processed in parallel.
 */
class MethodCallPass(cpg: Cpg, report: Report)
    extends ConcurrentWriterCpgPass[Call](cpg) {

  private val logger = LoggerFactory.getLogger(getClass)
  private final val methodMap: Map[(String, Int), Method] = generateMethodMap(cpg)

  /**
   * Only get those calls ending with a parameter list.
   *
   * @return calls ending with a parameter list.
   */
  override def generateParts(): Array[Call] = cpg.call.filter(_.code.endsWith(")")).toArray

  /**
   * Run method call pass on a call.
   *
   * @param diffGraph diff graph for creation
   * @param part      call node the method call pass is performed on
   */
  override def runOnPart(diffGraph: DiffGraphBuilder, part: Call): Unit = {
    val result = doMethodCallPass(part)
    result match {
      case Failure(exception) =>
        logger.warn(s"Failed to perform method call pass for call '${part.name}'!", exception)
      case Success(localDiff) =>
        logger.info(s"Processed method call pass for call '${part.name}'")
        diffGraph.absorb(localDiff)
    }
  }

  /**
   * Generate a map that assigns a method name and the number of parameters to a method node.
   *
   * @param cpg CPG to populate
   * @return map (method name, number of parameters) -> Method
   */
  private def generateMethodMap(cpg: Cpg): Map[(String, Int), Method] = {
    val methodArray = cpg.method.toArray
    val methodMap = new mutable.HashMap[(String, Int), Method]
    for (method <- methodArray) {
      val numberOfParameters = method.parameter.length
      methodMap.addOne((method.name, numberOfParameters), method)
    }
    methodMap.toMap
  }

  /**
   * Perform pass for a single call.
   * We already know that the calls ends with a parameter list.
   * We get the name of the called method by slicing the String between the last . and the last (.
   * The number of parameters equals the number of outgoing argument edges.
   * If we find a matching Method node in the map, we connect the current Call to it.
   *
   * @param call call node the method call pass is performed on
   * @return diff graph for creation
   */
  private def doMethodCallPass(call: Call): Try[DiffGraphBuilder] = {
    implicit val localDiff: DiffGraphBuilder = new DiffGraphBuilder
    Try {
      val name = call.code.slice(call.code.lastIndexOf('.')+1, call.code.lastIndexOf('('))
      val numberOfParameters = call.argumentOut.length
      val method = methodMap.get((name, numberOfParameters))
      if(method.isDefined) addCallEdge(call, method.get)
      localDiff
    }
  }

  /**
   * Add Call edge to the graph.
   *
   * @param fromCall  node the edge should start from
   * @param toMethod  node the edge should lead to
   * @param diffGraph diffGraph the edge is added to
   */
  private def addCallEdge(fromCall: Call, toMethod: Method)(implicit diffGraph: DiffGraphBuilder): Unit = {
    try {
      diffGraph.addEdge(fromCall, toMethod, EdgeTypes.CALL)
    } catch
      case _ =>
        logger.warn(s"Creating Call edge failed between '${fromCall.code}' and '${toMethod.name}'")
  }

}
