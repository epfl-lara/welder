package welder
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input._

import inox.InoxProgram

trait TypeParsers { self: Interpolator =>

  class TypeParser extends StdTokenParsers with PositionalErrors with StringContextParsers {

    type Tokens = Lexer.type

    override val lexical = Lexer

    import TypeIR._
    import lexical.{Hole => _, _}
    import program.symbols
    import program.trees

    def withPos(error: String, pos: Position) = ErrorLocation(error, pos).toString

    def p(c: Char): Parser[Token] = (elem(Parenthesis(c)) | elem(Punctuation(c))) withFailureMessage {
      (p: Position) => withPos("Expected character: " + c, p)
    }
    def kw(s: String): Parser[Token] = elem(Keyword(s)) withFailureMessage {
      (p: Position) => withPos("Expected keyword: " + s, p)
    }

    lazy val arrow = kw("=>") withFailureMessage {
      (p: Position) => withPos("Unexpected character. Arrow `=>` or end of type expected.", p)
    }

    lazy val typeExpression: Parser[Expression] = positioned(rep1sep(betweenArrows, arrow) ^^ {
      case tss => tss.reverse match {
        case returnTypes :: rest => {
          val retType = returnTypes match {
            case Seq(t) => t
            case ts     => Operation(Tuple, ts)
          }
          rest.foldLeft(retType) { case (to, froms) => Operation(Arrow, Seq(Operation(Group, froms), to)) }
        }
        case Nil => program.ctx.reporter.fatalError("Empty list of types.")  // Should never happen.
      }
    }) withFailureMessage {
      (p: Position) => withPos("Type expected.", p)
    }

    lazy val betweenArrows: Parser[List[Expression]] = (argumentTypes | uniqueType) withFailureMessage {
      (p: Position) => withPos("Expected type or group of types.", p)
    }

    lazy val uniqueType: Parser[List[Expression]] = (appliedType | parensType) ^^ {
      case t => List(t)
    }

    def endOfGroup(c: Char) = p(c) withFailureMessage {
      (p: Position) => withPos("Expected character `" + c + "`, or more types (separated by `,`).", p)
    }

    lazy val argumentTypes: Parser[List[Expression]] =
      (p('(') ~> commit(rep1sep(typeExpression, p(',')) <~ endOfGroup(')'))) withFailureMessage {
        (p: Position) => withPos("Group of arguments expected.", p)
      }
    lazy val parensType: Parser[Expression] = p('(') ~> typeExpression <~ p(')')

    lazy val name: Parser[Expression] = positioned(acceptMatch("Name", {
      case Embedded(t : trees.Type) => Literal(EmbeddedType(t))
      case Embedded(i : inox.Identifier) => Literal(EmbeddedIdentifier(i))
      case lexical.Identifier(s) => Literal(Name(s))
      case lexical.Hole(i) => Hole(i)
    }))

    lazy val appliedType: Parser[Expression] = for {
      n <- name
      oArgs <- opt(p('[') ~> rep1sep(typeExpression, p(',')) <~ endOfGroup(']'))
    } yield oArgs match {
      case None => n
      case Some(args) => Application(n, args)
    }

    lazy val inoxType: Parser[trees.Type] = (typeExpression ^^ toInoxType).flatMap { case e => e match {
      case Right(t) => success(t)
      case Left(es) => err(es.map(_.toString).mkString("\n\n"))
    }}
  }
}