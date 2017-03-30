package welder
package parsing

import scala.util.parsing.input.Position

case class ParsingException(error: String) extends Exception(error)

trait ElaborationException extends Exception {
  val errors: Seq[ErrorLocation]

  override def getMessage(): String = errors.map(_.toString).mkString("\n\n")
}

case class ExpressionElaborationException(errors: Seq[ErrorLocation]) extends ElaborationException
case class TypeElaborationException(errors: Seq[ErrorLocation]) extends ElaborationException
case class ConstraintException(error: String, position: Position) extends ElaborationException {
  override val errors = Seq(ErrorLocation(error, position))
}