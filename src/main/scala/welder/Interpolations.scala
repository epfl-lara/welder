/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.Identifier
import inox.InoxProgram

import welder.parsing._

import scala.util.parsing.combinator.Parsers

trait Interpolations { self: Theory =>
  
  import program.trees._

  private object Parser extends ExpressionParser(program) {

    import lexical._

    def parseIR(sc: StringContext, args: Seq[Any]): ParseResult[eir.Expression] = {
      phrase(expression)(getReader(sc, args))
    }

    def parseValDef(sc: StringContext, args: Seq[Any]): ParseResult[ValDef] = {
      phrase(inoxValDef)(getReader(sc, args))
    }

    def parseType(sc: StringContext, args: Seq[Any]): ParseResult[Type] = {
      phrase(inoxType)(getReader(sc, args))
    }
  }

  implicit class ExpressionInterpolator(sc: StringContext) {

    private def fromParseResult[A](result: Parser.ParseResult[A]): A =
      result match {
        case Parser.NoSuccess(msg, _) => throw new Exception(msg)
        case Parser.Success(value, _) => value
      }

    def e(args: Any*): Expr = {
      val ir = fromParseResult(Parser.parseIR(sc, args))
      Parser.eir.toInoxExpr(ir)
    }

    def ir(args: Any*): Any = {
      fromParseResult(Parser.parseIR(sc, args))
    }

    def v(args: Any*): ValDef = {
      fromParseResult(Parser.parseValDef(sc, args))
    }

    def r(args: Any*): Seq[Any] = {
      val reader = Parser.lexical.getReader(sc, args)

      import scala.util.parsing.input.Reader 

      def go[A](r: Reader[A]): Seq[A] = {
        if (r.atEnd) Seq()
        else r.first +: go(r.rest)
      }

      go(reader)
    }

    def t(args: Any*): Type = {
      fromParseResult(Parser.parseType(sc, args))
    }
  }
}
