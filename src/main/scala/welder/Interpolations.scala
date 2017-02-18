package welder

import inox.Identifier
import inox.trees
import inox.InoxProgram

import welder.parsing._

trait Interpolations { self: Theory =>
  
  import program.trees._

  private object ExpressionParser extends InoxParser(program) {

    import lexical._

    def parseExpr(sc: StringContext, args: Seq[Any], store: Store = Map()): ParseResult[Expr] = {
      phrase(expression(store))(getReader(sc, args))
    }

    def parseType(sc: StringContext, args: Seq[Any]): ParseResult[Type] = {
      phrase(inoxType)(getReader(sc, args))
    }

    def parseValDef(sc: StringContext, args: Seq[Any]): ParseResult[ValDef] = {
      phrase(valDef)(getReader(sc, args))
    }
  }

  implicit class ExpressionInterpolator(sc: StringContext) {

    def e(args: Any*): Attempt[Expr] = {
      ExpressionParser
        .parseExpr(sc, args)
        .map(Attempt.success(_))
        .getOrElse(Attempt.fail("No parse."))
    }

    def c(args: Any*): Attempt[Expr => Expr] = {
      val hole = Variable.fresh("_", Untyped)

      val parse = ExpressionParser
                    .parseExpr(sc, args, Map("_" -> hole))
                    .map(Attempt.success(_))
                    .getOrElse(Attempt.fail("No parse."))

      parse.map({ (withHole: Expr) =>
        (x: Expr) => exprOps.replaceFromSymbols(Map((hole -> x)), withHole)
      })
    }

    def v(args: Any*): Attempt[ValDef] = {
      ExpressionParser
        .parseValDef(sc, args)
        .map(Attempt.success(_))
        .getOrElse(Attempt.fail("No parse."))
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

    def t(args: Any*): Attempt[Type] = {
      ExpressionParser.parseType(sc, args)
                      .map(Attempt.success(_))
                      .getOrElse(Attempt.fail("No parse."))
    }
  }
}
