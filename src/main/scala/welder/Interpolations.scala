/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.Identifier
import inox.InoxProgram

import welder.parsing._

import scala.util.parsing.combinator.Parsers

trait Interpolations { self: Theory =>
  
  import program.trees._

  private object ExpressionParser extends ExpressionParser(program) {

    import lexical._

    def parseExpr(sc: StringContext, args: Seq[Any]): ParseResult[Expr] = {
      phrase(inoxExpr)(getReader(sc, args))
    }

    def parseIR(sc: StringContext, args: Seq[Any]): ParseResult[Any] = {
      phrase(expression)(getReader(sc, args))
    }

    def parseValDef(sc: StringContext, args: Seq[Any]): ParseResult[ValDef] = {
      phrase(inoxValDef)(getReader(sc, args))
    }
  }

  object TypeParser extends TypeParser(program) {

    import lexical._

    def parseType(sc: StringContext, args: Seq[Any]): ParseResult[program.trees.Type] = {
      phrase(inoxType)(getReader(sc, args))
    }
  }

  implicit class ExpressionInterpolator(sc: StringContext) {

    def fromParseResult[A](result: Parsers#ParseResult[A]): Attempt[A] =
      result match {
        case ExpressionParser.NoSuccess(msg, _) => Attempt.fail(msg)
        case ExpressionParser.Success(value, _) => Attempt.success(value)
      }

    def fromParseResultType[A](result: TypeParser.ParseResult[A]): Attempt[A] =
      result match {
        case TypeParser.NoSuccess(msg, _) => Attempt.fail(msg)
        case TypeParser.Success(value, _) => Attempt.success(value)
      }

    def e(args: Any*): Expr = {
      fromParseResult(ExpressionParser.parseExpr(sc, args))
    }

    def ir(args: Any*): Any = {
      fromParseResult(ExpressionParser.parseIR(sc, args))
    }

    // def c(args: Any*): Expr => Expr = {
    //   val hole = Variable.fresh("_", Untyped)

    //   val parse = fromParseResult(ExpressionParser.parseExpr(sc, args,))

    //   parse.map({ (withHole: Expr) =>
    //     (x: Expr) => exprOps.replaceFromSymbols(Map((hole -> x)), withHole)
    //   })
    // }

    def v(args: Any*): ValDef = {
      fromParseResult(ExpressionParser.parseValDef(sc, args))
    }

    // TODO: Remove. Just useful for internal debug.
    def r(args: Any*): List[Any] = {
      val reader = ExpressionParser.lexical.getReader(sc, args)

      import scala.util.parsing.input.Reader 

      def go[A](r: Reader[A]): List[A] = {
        if (r.atEnd) List()
        else r.first :: go(r.rest)
      }

      go(reader)
    }

    def t(args: Any*): Type = {
      fromParseResultType(TypeParser.parseType(sc, args))
    }
  }
}
