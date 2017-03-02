package welder
package parsing

trait IR {
  type Identifier
  type Type
  type Operator
  type Value
  type Field
  type Quantifier

  sealed abstract class Expression
  case class Variable(identifier: Identifier) extends Expression
  case class Application(callee: Expression, args: Seq[Expression]) extends Expression
  case class Abstraction(quantifier: Quantifier, bindings: Seq[(Identifier, Option[Type])], body: Expression) extends Expression
  case class Operation(operator: Operator, args: Seq[Expression]) extends Expression
  case class Selection(structure: Expression, field: Field) extends Expression
  case class Literal(value: Value) extends Expression
  case class TypeApplication(callee: Expression, args: Seq[Type]) extends Expression
  case class Let(bindings: Seq[(Identifier, Option[Type])], value: Expression, body: Expression) extends Expression
}
