/* Copyright 2017 EPFL, Lausanne */

package welder
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._

import inox.InoxProgram

// TODO: Infer types in some manner?

class InoxParser(val program: InoxProgram) extends StdTokenParsers {

  type Tokens = InoxLexer

  override val lexical = new InoxLexer(program)

  import program.trees._
  import lexical._

  implicit val symbols = program.symbols

  type Store = Map[String, Variable]

  def p(p: Char): Parser[Token] = elem(Parenthesis(p)) | elem(Punctuation(p))
  def kw(s: String): Parser[Token] = elem(Keyword(s))

  def expression(implicit store: Store): Parser[Expr] = greedyRight | operatorExpr
  def nonOperatorExpr(implicit store: Store): Parser[Expr] = greedyRight | selectionExpr

  def selectableExpr(implicit store: Store): Parser[Expr] = withApplication {
    invocationExpr | constructorExpr | literalExpr | variableExpr | parensExpr
  }

  def withApplication(exprParser: Parser[Expr])(implicit store: Store): Parser[Expr] =
    for {
      expr <- exprParser
      argss <- rep(arguments) 
    } yield {
      argss.foldLeft(expr) {
        case (acc, args) => Application(acc, args)
      }
    }

  def selectionExpr(implicit store: Store): Parser[Expr] = {
      
    val selector = for {
      i <- selectorIdentifier
      argss <- rep(arguments) 
    } yield { (expr: Expr) =>
      val zero: Expr = ADTSelector(expr, i)

      argss.foldLeft(zero) {
        case (acc, args) => Application(acc, args)
      }
    }

    val asInstOf = for {
      _ <- elem(Identifier("asInstanceOf"))
      _ <- p('[')
      tpe <- inoxType
      _ <- p(']')
    } yield { (x: Expr) => AsInstanceOf(x, tpe) }

    val isInstOf = for {
      _ <- elem(Identifier("isInstanceOf"))
      _ <- p('[')
      tpe <- inoxType
      _ <- p(']')
    } yield { (x: Expr) => IsInstanceOf(x, tpe) }

    selectableExpr ~ rep(kw(".") ~> (asInstOf | isInstOf | selector)) ^^ {
      case expr ~ funs => funs.foldLeft(expr) {
        case (acc, f) => f(acc)
      }
    }
  }

  lazy val selectorIdentifier: Parser[inox.Identifier] = acceptMatch("Selector identifier.", {
    case Identifier(name) => inox.FreshIdentifier(name)
    case RawIdentifier(i) => i
  })

  def greedyRight(implicit store: Store): Parser[Expr] = forallExpr | lambdaExpr

  val literalExpr: Parser[Expr] = acceptMatch("literal", {
    case Keyword("true")  => BooleanLiteral(true)
    case Keyword("false") => BooleanLiteral(false)
    case StringLit(s) => StringLiteral(s)
    case NumericLit(n) => IntegerLiteral(BigInt(n))
    case RawExpr(e) => e
  })

  def variableExpr(implicit store: Store): Parser[Variable] = acceptMatch("Unknown identifier.", {
    case Identifier(name) if store.contains(name) => store(name)
    case RawIdentifier(i) if store.contains(i.uniqueName) => store(i.uniqueName)
  })

  def parensExpr(implicit store: Store): Parser[Expr] = 
    (p('(') ~> expression <~ p(')')) |
    (p('{') ~> expression <~ p('}'))

  lazy val inoxIdentifier: Parser[(inox.Identifier, String)] = acceptMatch("Identifier.", {
    case Identifier(name) => (inox.FreshIdentifier(name), name)
    case RawIdentifier(i) => (i, i.uniqueName)
  })

  lazy val inoxType: Parser[Type] = rep1sep(argumentTypes | uniqueType, kw("=>")) ^^ {
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

  lazy val fdTable = symbols.functions.toSeq.map({
    case (i, fd) => i.name -> fd 
  }).toMap

  def funDef(implicit store: Store): Parser[FunDef] = acceptMatch("Unknown function.", {
    case Identifier(name) if fdTable.contains(name) => fdTable(name)
    case RawIdentifier(i) if symbols.functions.contains(i) => symbols.functions(i)
  })

  def arguments(implicit store: Store): Parser[List[Expr]] = 
    (p('(') ~> repsep(expression, p(',')) <~ p(')')) |
    (p('{') ~> (expression ^^ (List(_))) <~ p('}'))

  def invocationExpr(implicit store: Store): Parser[Expr] = for {
    fd <- funDef
    otps <- opt(typeArguments)
    if (otps.isEmpty || otps.get.size == fd.tparams.size)
    args <- arguments
    if (args.size == fd.params.size)
  } yield otps match {
    case Some(tps) => fd.typed(tps).applied(args)
    case None      => try {
      symbols.functionInvocation(fd, args)
    } catch {
      case e: Throwable => fd.typed.applied(args)
    }
  }

  lazy val cstrTable = symbols.adts.toSeq.collect({
    case (i, cstr: ADTConstructor) => i.name -> cstr
  }).toMap

  def cstrDef(implicit store: Store): Parser[ADTConstructor] = acceptMatch("Unknown constructor", {
    case Identifier(name) if cstrTable.contains(name) => cstrTable(name)
    case RawIdentifier(i) if symbols.adts.contains(i) && !symbols.adts(i).isSort =>
      symbols.adts(i).asInstanceOf[ADTConstructor]
  })

  def constructorExpr(implicit store: Store): Parser[Expr] = for {
    ct <- cstrDef
    otps <- opt(typeArguments)
    if (otps.isEmpty || otps.get.size == ct.tparams.size)
    args <- arguments
    if (args.size == ct.fields.size)
  } yield otps match {
    case Some(tps) => ADT(ct.typed(tps).toType, args)
    case None      => try {
      symbols.adtConstruction(ct, args)
    } catch {
      case e: Throwable => ADT(ct.typed.toType, args)
    }
  }

  lazy val typeArguments: Parser[List[Type]] = p('[') ~> rep1sep(inoxType, p(',')) <~ p(']')

  lazy val adtType: Parser[Type] = {

    val adtTable = symbols.adts.toSeq.map({
      case (i, d) => i.name -> d 
    }).toMap

    val adtDefinition: Parser[ADTDefinition] = acceptMatch("Unknown ADT.", {
      case Identifier(name) if adtTable.contains(name) => adtTable(name)
      case RawIdentifier(i) if symbols.adts.contains(i) => symbols.adts(i)
    })

    def params(n: Int): Parser[List[Type]] = {
      if (n == 0) {
        success(List())
      }
      else {
        typeArguments ^? {
          case ts if ts.size == n => ts
        }
      }
    }

    for {
      d <- adtDefinition
      ts <- params(d.tparams.size)
    } yield d.typed(ts).toType
  }

  lazy val compoundType: Parser[Type] = {
    val map = elem(Identifier("Map")) ~> typeArguments ^? {
      case List(k, v) => MapType(k, v)
    }

    val set = elem(Identifier("Set")) ~> typeArguments ^? {
      case List(v) => SetType(v)
    }

    val bag = elem(Identifier("Bag")) ~> typeArguments ^? {
      case List(v) => BagType(v)
    }

    map | set | bag
  }

  lazy val valDef: Parser[ValDef] = for {
    (i, _) <- inoxIdentifier
    _ <- p(':')
    t <- inoxType
  } yield ValDef(i, t)

  lazy val valDefs: Parser[List[(ValDef, String)]] = for {
    ins <- rep1sep(inoxIdentifier, p(','))
    _ <- p(':')
    t <- inoxType
  } yield ins.map({ case (i, n) => (ValDef(i, t), n) })

  def forallExpr(implicit store: Store): Parser[Expr] = for {
    _ <- elem(Quantifier("forall"))
    vns <- rep1sep(valDefs, p(',')).map(_.flatten)
    _ <- p('.')
    e <- expression(store ++ vns.map({ case (vd, n) => n -> vd.toVariable }))
  } yield Forall(vns.map(_._1), e)

  def lambdaExpr(implicit store: Store): Parser[Expr] = for {
    _ <- elem(Quantifier("lambda"))
    vns <- rep1sep(valDefs, p(',')).map(_.flatten)
    _ <- p('.')
    e <- expression(store ++ vns.map({ case (vd, n) => n -> vd.toVariable }))
  } yield Lambda(vns.map(_._1), e)

  def operatorExpr(implicit store: Store): Parser[Expr] = {

    def withPrio(oneOp: Parser[(Expr, Expr) => Expr], lessPrio: Parser[Expr]) = {
      lessPrio ~ rep(oneOp ~ lessPrio) ^^ { case lhs ~ opsAndRhs => 
        opsAndRhs.foldLeft(lhs) { case (lhs, op ~ rhs) => op(lhs, rhs) }
      }
    }

    // TODO: Add stuff here.
    val zero = nonOperatorExpr

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