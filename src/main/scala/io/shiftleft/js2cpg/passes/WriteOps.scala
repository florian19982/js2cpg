package io.shiftleft.js2cpg.passes

import io.shiftleft.codepropertygraph.generated.Operators

/**
 * Helper Object containing all writing calls.
 */
object WriteOps {

  /**
   * Collection of all writing Calls.
   *
   * @param operation name of the writing operation
   * @param position  position of the identifier
   * @param reading   if operation is also reading the identifier
   */
  case class IdentifierWrite(operation: String,
                             position: Int,
                             reading: Boolean)

  /**
   * The actual collection of all [[WriteOps.IdentifierWrite]]
   */
  val writes: Set[IdentifierWrite] = Set(
    IdentifierWrite(Operators.assignment, 1, reading = false),
  )

}
