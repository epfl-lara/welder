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

    private val parser = new ExpressionParser()

    def e(args: Any*): Expr = {
      ExprIR.getExpr(ir(args : _*))
    }

    def ir(args: Any*): ExprIR.Expression = {
      parser.getFromSC(sc, args)(parser.phrase(parser.expression))
    }

    def v(args: Any*): ValDef = {
      parser.getFromSC(sc, args)(parser.phrase(parser.inoxValDef))
    }

    def r(args: Any*): Seq[Lexer.Token] = {
      val reader = Lexer.getReader(sc, args)

      import scala.util.parsing.input.Reader 

      def go[A](r: Reader[A]): Seq[A] = {
        if (r.atEnd) Seq()
        else r.first +: go(r.rest)
      }

      go(reader)
    }

    def t(args: Any*): Type = {
      parser.getFromSC(sc, args)(parser.phrase(parser.inoxType))
    }
  }
}
