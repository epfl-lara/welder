package welder
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._

import inox.InoxProgram

import welder.parsing._

class ExpressionParser(program: InoxProgram) extends TypeParser(program) {

  import lexical.{Identifier => _, Quantifier => _, _}

  val eir = new ExprIR {
    override val trees = program.trees
    override val symbols = program.symbols
  }

  import eir._

  lazy val expression: Parser[Expression] = (greedyRight | operatorExpr) withFailureMessage "Expression expected."
  lazy val nonOperatorExpr: Parser[Expression] = greedyRight | selectionExpr

  lazy val selectableExpr: Parser[Expression] = withApplication {
    invocationExpr | literalExpr | variableExpr | parensExpr
  } withFailureMessage "Expression expected."

  def withApplication(exprParser: Parser[Expression]): Parser[Expression] =
    for {
      expr <- exprParser
      argss <- rep(arguments) 
    } yield {
      argss.foldLeft(expr) {
        case (acc, args) => Application(acc, args)
      }
    }

  lazy val selectionExpr: Parser[Expression] = {
      
    val selector = for {
      i <- selectorIdentifier
      targs <- opt(typeArguments)
      argss <- rep(arguments) 
    } yield { (expr: Expression) =>
      val zero: Expression = if (targs.isDefined) {
        TypeApplication(Selection(expr, i), targs.get)
      } else {
        Selection(expr, i)
      } 

      argss.foldLeft(zero) {
        case (acc, args) => Application(acc, args)
      }
    }

    selectableExpr ~ rep(kw(".") ~> selector) ^^ {
      case expr ~ funs => funs.foldLeft(expr) {
        case (acc, f) => f(acc)
      }
    }
  } withFailureMessage "Expression expected."

  lazy val selectorIdentifier: Parser[Field] = acceptMatch("Selector expected.", {
    case lexical.Identifier(name) => FieldName(name)
    case RawIdentifier(i) => FieldIdentifier(i)
  })

  lazy val greedyRight: Parser[Expression] = quantifierExpr | ifExpr

  lazy val ifExpr: Parser[Expression] = for {
    _ <- kw("if")
    c <- parensExpr
    t <- expression
    _ <- kw("else")
    e <- expression
  } yield Operation("IfThenElse", Seq(c, t, e))

  lazy val literalExpr: Parser[Expression] = acceptMatch("Literal expected.", {
    case Keyword("true")  => BooleanLiteral(true)
    case Keyword("false") => BooleanLiteral(false)
    case StringLit(s) => StringLiteral(s)
    case NumericLit(n) => NumericLiteral(n)
    case RawExpr(e) => EmbeddedExpr(e)
  }) ^^ (Literal(_))

  lazy val variableExpr: Parser[Expression] = identifier ^^ (Variable(_))

  lazy val identifier: Parser[Identifier] = acceptMatch("Identifier expected.", {
    case lexical.Identifier(name) => IdentifierName(name)
    case RawIdentifier(i) => IdentifierIdentifier(i)
  })

  lazy val parensExpr: Parser[Expression] = 
    (p('(') ~> expression <~ p(')')) |
    (p('{') ~> expression <~ p('}'))

  lazy val fdTable = symbols.functions.keys.toSet

  lazy val cstrTable = symbols.adts.toSeq.collect({
    case (i, cstr: trees.ADTConstructor) => i
  }).toSet

  val symbolTable = fdTable ++ cstrTable

  lazy val symbol: Parser[Expression] = acceptMatch("Function expected.", {
    case lexical.Identifier(name) if symbolTable.map(_.name).contains(name) => Literal(Name(name))
    case RawIdentifier(i) if symbolTable.contains(i) => Literal(EmbeddedIdentifier(i))
  })

  lazy val arguments: Parser[List[Expression]] = 
    (p('(') ~> repsep(expression, p(',')) <~ p(')')) |
    (p('{') ~> (expression ^^ (List(_))) <~ p('}'))

  lazy val invocationExpr: Parser[Expression] = for {
    sb <- symbol
    otps <- opt(typeArguments)
    args <- arguments
  } yield otps match {
    case Some(tps) => Application(TypeApplication(sb, tps), args)
    case None => Application(sb, args)
  }

  lazy val quantifier: Parser[Quantifier] = acceptMatch("Quantifier expected.", {
    case lexical.Quantifier("forall") => Forall
    case lexical.Quantifier("lambda") => Lambda
  })

  lazy val valDef: Parser[(Identifier, Option[trees.Type])] = for {
    i <- identifier
    otype <- opt(p(':') ~> inoxType)
  } yield (i, otype)

  def quantifierExpr: Parser[Expression] = for {
    q <- quantifier
    vds <- rep1sep(valDef, p(','))
    _ <- p('.')
    e <- expression
  } yield Abstraction(q, vds, e)

  lazy val operatorExpr: Parser[Expression] = {

    def withPrio(oneOp: Parser[(Expression, Expression) => Expression], lessPrio: Parser[Expression], assoc: Assoc) = {
      assoc match {
        case LeftAssoc => {
          chainl1(lessPrio, oneOp)
        }
        case RightAssoc => {
          lessPrio ~ rep(oneOp ~ lessPrio) ^^ {
            case first ~ opsAndExprs => {
              if (opsAndExprs.isEmpty) {
                first
              }
              else {
                val (ops, exprs) = opsAndExprs.map({ case a ~ b => (a, b) }).unzip
                val exprsAndOps = (first +: exprs).zip(ops)
                val last = exprs.last

                exprsAndOps.foldRight(last) {
                  case ((expr, op), acc) => op(expr, acc)
                }
              }
            }
          }
        }
      }
    }

    val zero = nonOperatorExpr

    opTable.foldLeft(zero) {
      case (lessPrio, (ops, assoc)) => {
        val oneOp = ops.map({
          case op => elem(Operator(op)) ^^^ { (a: Expression, b: Expression) => Operation(op, Seq(a, b)) }
        }).reduce(_ | _)

        withPrio(oneOp, lessPrio, assoc)
      }
    }
  }

  lazy val typeArguments: Parser[List[Type]] = p('[') ~> rep1sep(inoxType, p(',')) <~ p(']')

  lazy val inoxExpr: Parser[trees.Expr] = expression ^? irToInoxExpr
  lazy val irToInoxExpr: PartialFunction[Expression, trees.Expr] = Utils.toPartial(toInoxExpr(_))
}