/* Copyright 2017 EPFL, Lausanne */

package welder
package parsing

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._

import inox.InoxProgram

class InoxLexer(val program: InoxProgram) extends StdLexical with StringContextLexer {

  reserved ++= Seq("true", "false", "if", "else")

  import program.trees._

  val unaryOps: Seq[String] = Seq("-", "+", "!")
  val opTable: Seq[(Seq[String], Assoc)] = Seq(

    Seq("*", "/", "%", "mod") -> LeftAssoc,

    Seq("+", "-") -> LeftAssoc,
    
    Seq(">=", "<=", ">", "<") -> LeftAssoc,

    Seq("==", "!=") -> LeftAssoc,

    Seq("&&", "&") -> LeftAssoc,

    Seq("||", "|") -> LeftAssoc,

    Seq("==>") -> RightAssoc
  )
  val operators = (opTable.map(_._1).flatten ++ unaryOps).distinct

  case class Parenthesis(parenthesis: Char) extends Token { def chars = parenthesis.toString }
  case class Punctuation(punctuation: Char) extends Token { def chars = punctuation.toString }
  case class Quantifier(quantifier: String) extends Token { def chars = quantifier }
  case class Operator(operator: String) extends Token { def chars = operator }
  case class RawIdentifier(identifier: inox.Identifier) extends Token { def chars = identifier.name }
  case class RawExpr(expr: Expr) extends Token { def chars = expr.toString }
  case class RawType(tpe: Type) extends Token { def chars = tpe.toString }

  override def token: Parser[Token] = keywords | punctuation | parens | operator | quantifier | super.token

  val keywords = acceptSeq("=>") ^^^ Keyword("=>") |
                 ('.' <~ not(whitespaceChar)) ^^^ Keyword(".") |
                 acceptSeq("true") ^^^ Keyword("true") |
                 acceptSeq("false") ^^^ Keyword("false") |
                 acceptSeq("if") ^^^ Keyword("if") |
                 acceptSeq("else") ^^^ Keyword("else")

  val comma: Parser[Token] = ',' ^^^ Punctuation(',')
  val dot: Parser[Token] = '.' ^^^ Punctuation('.')
  val colon: Parser[Token] = ':' ^^^ Punctuation(':')
  val punctuation: Parser[Token] = comma | dot | colon

  val quantifier: Parser[Token] = '∀' ^^^ Quantifier("forall") |
                                  '∃' ^^^ Quantifier("exists") |
                                  'λ' ^^^ Quantifier("lambda")


  val operator: Parser[Token] =
    operators.sortBy(-_.length).map(acceptSeq(_)).reduce(_ | _) ^^ { (xs: List[Char]) =>
      Operator(xs.mkString)
    }

  val parens: Parser[Token] = accept("parenthesis", {
      case c@('[' | ']' | '(' | ')' | '{' | '}') => Parenthesis(c)
    })

  override def argToToken(x: Any): Token = x match {
    case s: Symbol  => Identifier(s.toString)
    case i: BigInt  => NumericLit(i.toString)
    case i: Int     => NumericLit(i.toString)
    case b: Boolean => RawExpr(BooleanLiteral(b))
    case s: String  => StringLit(s)
    case i: inox.Identifier => RawIdentifier(i)
    case e: Expr => RawExpr(e)
    case t: Type => RawType(t)
    case _ => ErrorToken("Invalid element: " + x)
  }
}