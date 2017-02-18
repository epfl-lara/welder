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

    def fromParseResult[A](result: ExpressionParser.ParseResult[A]): Attempt[A] =
      result match {
        case ExpressionParser.NoSuccess(msg, _) => Attempt.fail(msg)
        case ExpressionParser.Success(value, _) => Attempt.success(value)
      }

    def e(args: Any*): Expr = {
      fromParseResult(ExpressionParser.parseExpr(sc, args))
    }

    def c(args: Any*): Expr => Expr = {
      val hole = Variable.fresh("_", Untyped)

      val parse = fromParseResult(ExpressionParser.parseExpr(sc, args, Map("_" -> hole)))

      parse.map({ (withHole: Expr) =>
        (x: Expr) => exprOps.replaceFromSymbols(Map((hole -> x)), withHole)
      })
    }

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
      fromParseResult(ExpressionParser.parseType(sc, args))
    }
  }
}
