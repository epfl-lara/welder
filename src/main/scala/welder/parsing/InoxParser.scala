package welder
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._

import inox.InoxProgram

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

  lazy val inoxType: Parser[Type] = rep1sep(argumentTypes | uniqueType, elem(Keyword("=>"))) ^^ {
    case tss => tss.reverse match {
      case returnTypes :: rest => {
        val retType = returnTypes match {
          case Seq(t) => t
          case ts     => TupleType(ts)
        }
        rest.foldLeft(retType) { case (to, froms) => FunctionType(froms, to) }
      }
      case Nil => program.ctx.reporter.fatalError("inoxType: Empty list of types.")  // Should never happen.
    }
  }

  lazy val uniqueType: Parser[List[Type]] = (basicTypes | adtType | compoundType | rawType | parensType) ^^ {
    case t => List(t)
  }

  lazy val rawType: Parser[Type] = acceptMatch("Not a type.", {
    case RawType(t) => t
  })

  lazy val argumentTypes: Parser[List[Type]] = p('(') ~> rep1sep(inoxType, p(',')) <~ p(')')

  lazy val parensType: Parser[Type] = p('(') ~> inoxType <~ p(')')

  lazy val basicTypes: Parser[Type] = {

    val table = Seq(
      "Boolean" -> BooleanType,
      "BigInt"  -> IntegerType,
      "Char"    -> CharType,
      "Int"     -> Int32Type,
      "Real"    -> RealType,
      "String"  -> StringType,
      "Unit"    -> UnitType)

    val conversion: PartialFunction[Token, Type] =
      table.map({ case (name, tpe) => Identifier(name) -> tpe }).toMap
    acceptMatch("Unknown type.", conversion)
  }

  lazy val typeParameters: Parser[List[Type]] = p('[') ~> rep1sep(inoxType, p(',')) <~ p(']')

  lazy val adtType: Parser[Type] = {

    val adtTable = program.symbols.adts.toSeq.map({
      case (i, d) => i.name -> d 
    }).toMap

    val adtDefinition: Parser[ADTDefinition] = acceptMatch("Unknown ADT.", {
      case Identifier(name) if adtTable.contains(name) => adtTable(name)
      case RawIdentifier(i) if program.symbols.adts.contains(i) => program.symbols.adts(i)
    })

    def params(n: Int): Parser[List[Type]] = {
      if (n == 0) {
        success(List())
      }
      else {
        typeParameters ^? {
          case ts if ts.size == n => ts
        }
      }
    }

    for {
      d <- adtDefinition
      ts <- params(d.tparams.size)
    } yield d.typed(ts)(program.symbols).toType
  }

  lazy val compoundType: Parser[Type] = {
    val map = elem(Identifier("Map")) ~> typeParameters ^? {
      case List(k, v) => MapType(k, v)
    }

    val set = elem(Identifier("Set")) ~> typeParameters ^? {
      case List(v) => SetType(v)
    }

    val bag = elem(Identifier("Bag")) ~> typeParameters ^? {
      case List(v) => BagType(v)
    }

    map | set | bag
  }

  lazy val valDefs: Parser[List[(ValDef, String)]] = for {
    ins <- rep1sep(inoxIdentifier, p(','))
    _ <- elem(Punctuation(':'))
    t <- inoxType
  } yield ins.map({ case (i, n) => (ValDef(i, t), n) })

  def forallExpr(implicit store: Store): Parser[Expr] = for {
    _ <- elem(Quantifier("forall"))
    vns <- rep1sep(valDefs, p(',')).map(_.flatten)
    _ <- elem(Punctuation('.'))
    e <- expression(store ++ vns.map({ case (vd, n) => n -> vd.toVariable }))
  } yield Forall(vns.map(_._1), e)

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