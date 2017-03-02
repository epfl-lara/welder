package welder
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._

import inox.InoxProgram

class TypeIRParser(val program: InoxProgram) extends StdTokenParsers {

  type Tokens = InoxLexer

  override val lexical = new InoxLexer(program)

  val tir = new TypeIR {
    override val trees = program.trees
    override val symbols = program.symbols
  }

  import tir._
  import lexical._

  val symbols = program.symbols

  def p(p: Char): Parser[Token] = elem(Parenthesis(p)) | elem(Punctuation(p))
  def kw(s: String): Parser[Token] = elem(Keyword(s))

  lazy val typeExpression: Parser[Expression] = rep1sep(argumentTypes | uniqueType, kw("=>")) ^^ {
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
  } withErrorMessage "Type expected."

  lazy val uniqueType: Parser[List[Expression]] = (appliedType | parensType) ^^ {
    case t => List(t)
  }

  lazy val argumentTypes: Parser[List[Expression]] = p('(') ~> rep1sep(typeExpression, p(',')) <~ p(')')

  lazy val parensType: Parser[Expression] = p('(') ~> typeExpression <~ p(')')

  lazy val name: Parser[Expression] = acceptMatch("Non-function type expected.", {
    case RawType(t) => Literal(EmbeddedType(t))
    case RawIdentifier(i) => Literal(EmbeddedIdentifier(i))
    case lexical.Identifier(s) => Literal(Name(s))
  })

  lazy val appliedType: Parser[Expression] = for {
    n <- name
    oArgs <- opt(p('[') ~> rep1sep(typeExpression, p(',')) <~ p(']'))
  } yield oArgs match {
    case None => n
    case Some(args) => Application(n, args)
  }

  lazy val inoxType: Parser[trees.Type] = typeExpression ^? irToInoxType
  lazy val irToInoxType: PartialFunction[Expression, trees.Type] = Utils.toPartial(toInoxType(_))
}