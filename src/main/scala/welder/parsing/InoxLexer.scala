package welder
package parsing

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._

import inox.InoxProgram

class InoxLexer(val program: InoxProgram) extends StdLexical with StringContextLexer {

  import program.trees._

  val opTable: Seq[Seq[(String, (Expr, Expr) => Expr)]] = Seq(

    Seq("*" -> { (a: Expr, b: Expr) => Times(a, b) },
        "/" -> { (a: Expr, b: Expr) => Division(a, b) },
        "%" -> { (a: Expr, b: Expr) => Remainder(a, b) }),

    Seq("+" -> { (a: Expr, b: Expr) => Plus(a, b) }, 
        "-" -> { (a: Expr, b: Expr) => Minus(a, b) }),
    
    Seq(">=" -> { (a: Expr, b: Expr) => GreaterEquals(a, b) },
        "<=" -> { (a: Expr, b: Expr) => LessEquals(a, b) },
        ">" -> { (a: Expr, b: Expr) => GreaterThan(a, b) },
        "<" -> { (a: Expr, b: Expr) => LessThan(a, b) }),

    Seq("==" -> { (a: Expr, b: Expr) => Equals(a, b) },
        "!=" -> { (a: Expr, b: Expr) => Not(Equals(a, b)) }),

    Seq("&&" -> { (a: Expr, b: Expr) => And(a, b) }),

    Seq("||" -> { (a: Expr, b: Expr) => Or(a, b) })
  )
  val operators = opTable.flatten.map(_._1)

  case class Parenthesis(parenthesis: Char) extends Token { def chars = parenthesis.toString }
  case class Punctuation(punctuation: Char) extends Token { def chars = punctuation.toString }
  case class Quantifier(quantifier: String) extends Token { def chars = quantifier }
  case class Operator(operator: String) extends Token { def chars = operator }
  case class RawIdentifier(identifier: inox.Identifier) extends Token { def chars = identifier.name }
  case class RawExpr(expr: Expr) extends Token { def chars = expr.toString }
  case class RawType(tpe: Type) extends Token { def chars = tpe.toString }

  override def token: Parser[Token] = keywords | punctuation | parens | operator | quantifier | super.token

  val keywords = acceptSeq("=>") ^^^ Keyword("=>")

  val comma: Parser[Token] = ',' ^^^ Punctuation(',')
  val dot: Parser[Token] = '.' ^^^ Punctuation('.')
  val colon: Parser[Token] = ':' ^^^ Punctuation(':')
  val punctuation: Parser[Token] = comma | dot | colon

  val quantifier: Parser[Token] = '∀' ^^^ Quantifier("forall")

  val operator: Parser[Token] =
    operators.map(acceptSeq(_)).reduce(_ | _) ^^ { (xs: List[Char]) =>
      Operator(xs.mkString)
    }

  val parens: Parser[Token] = accept("parenthesis", {
      case c@('[' | ']' | '(' | ')' | '{' | '}') => Parenthesis(c)
    })

  override def argToToken(x: Any): Token = x match {
    case s: Symbol => Identifier(s.toString)
    case i: BigInt => NumericLit(i.toString)
    case i: Int    => NumericLit(i.toString)
    case s: String => StringLit(s)
    case i: inox.Identifier => RawIdentifier(i)
    case e: Expr => RawExpr(e)
    case t: Type => RawType(t)
    case _ => ErrorToken("Invalid element: " + x)
  }
}