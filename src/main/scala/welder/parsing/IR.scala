package welder
package parsing

/** Contains abstract Intermediate Representation (IR) language. */ 
trait IR {

  type Identifier  // Identifier of the language.
  type Type        // Types.
  type Operator    // Primitive operators.
  type Value       // Literal values.
  type Field       // Fields.
  type Quantifier  // Quantifiers.

  sealed abstract class Expression
  case class Variable(identifier: Identifier) extends Expression
  case class Application(callee: Expression, args: Seq[Expression]) extends Expression
  case class Abstraction(quantifier: Quantifier, bindings: Seq[(Identifier, Option[Type])], body: Expression) extends Expression
  case class Operation(operator: Operator, args: Seq[Expression]) extends Expression
  case class Selection(structure: Expression, field: Field) extends Expression
  case class Literal(value: Value) extends Expression
  case class TypeApplication(callee: Expression, args: Seq[Type]) extends Expression
  case class Let(bindings: Seq[(Identifier, Option[Type], Expression)], body: Expression) extends Expression
}
