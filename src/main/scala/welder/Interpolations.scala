/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.Identifier
import inox.InoxProgram

import welder.parsing._

import scala.util.parsing.combinator.Parsers

trait Interpolations { self: Theory =>
  
  import program.trees._

  lazy val interpolator = new Interpolator {
    override val program = self.program
  }

  implicit class ExpressionInterpolator(sc: StringContext) {

    import interpolator._

    class Parser extends ExpressionParser {

      import lexical._

      def parseIR(sc: StringContext, args: Seq[Any]): ParseResult[ExprIR.Expression] = {
        phrase(expression)(getReader(sc, args))
      }

      def parseValDef(sc: StringContext, args: Seq[Any]): ParseResult[ValDef] = {
        phrase(inoxValDef)(getReader(sc, args))
      }

      def parseType(sc: StringContext, args: Seq[Any]): ParseResult[Type] = {
        phrase(inoxType)(getReader(sc, args))
      }
    }

    val parser = new Parser()

    private def fromParseResult[A](result: parser.ParseResult[A]): A =
      result match {
        case parser.NoSuccess(msg, _) => throw new Exception(msg)
        case parser.Success(value, _) => value
      }

    def e(args: Any*): Expr = {
      val ir = fromParseResult(parser.parseIR(sc, args))
      ExprIR.toInoxExpr(ir)
    }

    def ir(args: Any*): Any = {
      fromParseResult(parser.parseIR(sc, args))
    }

    def v(args: Any*): ValDef = {
      fromParseResult(parser.parseValDef(sc, args))
    }

    def r(args: Any*): Seq[Any] = {
      val reader = parser.lexical.getReader(sc, args)

      import scala.util.parsing.input.Reader 

      def go[A](r: Reader[A]): Seq[A] = {
        if (r.atEnd) Seq()
        else r.first +: go(r.rest)
      }

      go(reader)
    }

    def t(args: Any*): Type = {
      fromParseResult(parser.parseType(sc, args))
    }
  }
}
