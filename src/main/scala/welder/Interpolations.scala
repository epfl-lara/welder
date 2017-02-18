package welder

import inox.Identifier
import inox.trees
import inox.InoxProgram

import welder.parsing._

trait Interpolations { self: Theory =>
  
  import program.trees._

  object ExpressionParser extends InoxParser(program) {

    import lexical._

    def parseExpr(sc: StringContext, args: Seq[Any]): ParseResult[Expr] = {
      phrase(expression(Map()))(getReader(sc, args))
    }

    def parseType(sc: StringContext, args: Seq[Any]): ParseResult[Type] = {
      phrase(inoxType)(getReader(sc, args))
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
      ExpressionParser.parseExpr(sc, args)
                      .map(Attempt.success(_))
                      .getOrElse(Attempt.fail("No parse."))
    }

    def r(args: Any*): List[ExpressionParser.lexical.Token] = {
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
