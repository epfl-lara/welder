package welder

import scala.collection.mutable.HashSet
import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input._

import inox.Identifier
import inox.trees
import inox.InoxProgram

import welder.util.StringContextLexer

trait Interpolations { self: Theory =>
  
  import program.trees._

  object ExpressionParser extends InoxParser(program) {

    import lexical._

    def apply(sc: StringContext, args: Seq[Any]): ParseResult[Expr] = {
      phrase(expression(Map()))(getReader(sc, args))
    }
  }

  // object ExpressionInterpolator {
  //   lazy val functions: Map[String, Seq[Identifier]] = {
  //     program.symbols.functions.keySet.groupBy(_.name).map({ case (n, is) =>
  //       n -> is.toSeq
  //     }).toMap
  //   }
  // }

  implicit class ExpressionInterpolator(sc: StringContext) {

    def e(args: Any*): Attempt[Expr] = {
      ExpressionParser(sc, args).map(Attempt.success(_)).getOrElse(Attempt.fail("No parse."))
    }

    def r(args: Any*): List[ExpressionParser.lexical.Token] = {
      val reader = ExpressionParser.lexical.getReader(sc, args)

      def go[A](r: Reader[A]): List[A] = {
        if (r.atEnd) List()
        else r.first :: go(r.rest)
      }

      go(reader)
    }
  }
}

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

  override def token: Parser[Token] = punctuation | parens | operator | quantifier | super.token

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


class InoxParser(val program: InoxProgram) extends StdTokenParsers {

  type Tokens = InoxLexer

  override val lexical = new InoxLexer(program)

  import program.trees._
  import lexical._

  type Store = Map[String, Variable]

  def expression(implicit store: Store): Parser[Expr] = forallExpr | operatorExpr

  val literalExpr: Parser[Expr] = acceptMatch("literal", {
    case StringLit(s) => StringLiteral(s)
    case NumericLit(n) => IntegerLiteral(BigInt(n))
    case RawExpr(e) => e
  })

  def variableExpr(implicit store: Store): Parser[Variable] = acceptMatch("Unknown identifier.", {
    case Identifier(name) if store.contains(name) => store(name)
    case RawIdentifier(i) if store.contains(i.uniqueName) => store(i.uniqueName)
  })

  def p(p: Char): Parser[Token] = elem(Parenthesis(p)) | elem(Punctuation(p))

  def parensExpr(implicit store: Store): Parser[Expr] = 
    (p('(') ~> expression <~ p(')')) |
    (p('{') ~> expression <~ p('}'))

  lazy val inoxIdentifier: Parser[(inox.Identifier, String)] = acceptMatch("Identifier.", {
    case Identifier(name) => (inox.FreshIdentifier(name), name)
    case RawIdentifier(i) => (i, i.uniqueName)
  })

  lazy val inoxType: Parser[Type] = {

    // TODO: Complete this.
    val basicTypes = Seq(
      "Boolean" -> BooleanType, 
      "BigInt" -> IntegerType)

    val conversion: PartialFunction[Token, Type] =
      basicTypes.map({ case (name, tpe) => Identifier(name) -> tpe }).toMap
    acceptMatch("Unknown type.", conversion)
  }

  def forallExpr(implicit store: Store): Parser[Expr] = for {
    _ <- elem(Quantifier("forall"))
    (i, n) <- inoxIdentifier
    _ <- elem(Punctuation(':'))
    t <- inoxType
    _ <- elem(Punctuation('.'))
    e <- expression(store + (n -> new Variable(i, t, Set())))
  } yield Forall(Seq(ValDef(i, t)), e)

  def operatorExpr(implicit store: Store): Parser[Expr] = {

    def withPrio(oneOp: Parser[(Expr, Expr) => Expr], lessPrio: Parser[Expr]) = {
      lessPrio ~ rep(oneOp ~ lessPrio) ^^ { case lhs ~ opsAndRhs => 
        opsAndRhs.foldLeft(lhs) { case (lhs, op ~ rhs) => op(lhs, rhs) }
      }
    }

    // TODO: Add stuff here.
    val zero = forallExpr | literalExpr | variableExpr | parensExpr

    opTable.foldLeft(zero) {
      case (lessPrio, ops) => {
        val oneOp = ops.map({
          case (op, f) => elem(lexical.Operator(op)) ^^^ f
        }).reduce(_ | _)

        withPrio(oneOp, lessPrio)
      }
    }
  }
}