package welder
package parsing

trait ExpressionExtractors { self: Interpolator =>

  trait ExpressionExtractor extends Extractor { self: ExprIR.type => 

    import program.trees
    import program.symbols

    def extract(expr: trees.Expr, template: Expression)(implicit store: Map[String, inox.Identifier]): Option[Match] = {

      template match {
        case Hole(index) => return Some(Map(index -> expr))
        case TypeApplication(Operation("TypeAnnotation", Seq(templateInner)), Seq(templateType)) => for {
          matchingsType <- TypeIR.extract(expr.getType, templateType)
          mappingsInner <- extract(expr, templateInner)
        } yield matchingsType ++ mappingsInner
        case _ => ()
      }

      expr match {
        case trees.BooleanLiteral(bool) => template match {
          case Literal(BooleanLiteral(`bool`)) => success
          case _ => fail
        }
        case trees.IntegerLiteral(value) => template match {
          case Literal(NumericLiteral(string)) if (scala.util.Try(BigInt(string)).toOption == Some(value)) => success
          case _ => fail
        }
        case trees.CharLiteral(char) => template match {
          case Literal(CharLiteral(`char`)) => success
          case _ => fail 
        }
        case trees.BVLiteral(value, _) => template match {
          case Literal(NumericLiteral(string)) if (scala.util.Try(BigInt(string)).toOption == Some(value)) => success
          case _ => fail
        }
        case trees.FractionLiteral(numerator, denominator) => template match {
          case Literal(NumericLiteral(string)) if { val (n, d) = Utils.toFraction(string); n * denominator == d * numerator } => success
          case _ => fail
        }
        case trees.UnitLiteral() => template match {
          case Literal(UnitLiteral) => success
          case _ => fail
        }
        case trees.StringLiteral(string) => template match {
          case Literal(StringLiteral(`string`)) => success
          case _ => fail
        }
        case trees.Equals(left, right) => template match {
          case Operation("==", Seq(templateLeft, templateRight)) => for {
            mappingsLeft <- extract(left, templateLeft)
            mappingsRight <- extract(right, templateRight)
          } yield mappingsLeft ++ mappingsRight
          case _ => fail
        }
        case trees.And(exprs) => template match {
          case Operation("&&", templates) if (exprs.length == templates.length) => for {
            allMappings <- Utils.traverse(exprs.zip(templates).map { case (e, t) => extract(e, t) })
          } yield allMappings.fold(empty)(_ ++ _)
          case _ => fail
        }
        case trees.Or(exprs) => template match {
          case Operation("||", templates) if (exprs.length == templates.length) => for {
            allMappings <- Utils.traverse(exprs.zip(templates).map { case (e, t) => extract(e, t) })
          } yield allMappings.fold(empty)(_ ++ _)
          case _ => fail
        }
        case trees.Implies(left, right) => template match {
          case Operation("==>", Seq(templateLeft, templateRight)) => for {
            mappingsLeft <- extract(left, templateLeft)
            mappingsRight <- extract(right, templateRight)
          } yield mappingsLeft ++ mappingsRight
          case _ => fail
        }
        case trees.Not(inner) => template match {
          case Operation("!", Seq(templateInner)) => extract(inner, templateInner)
          case _ => fail
        }
        case trees.StringConcat(left, right) => template match {
          case ConcatenateOperation(templateLeft, templateRight) => for {
            mappingsLeft <- extract(left, templateLeft)
            mappingsRight <- extract(right, templateRight)
          } yield mappingsLeft ++ mappingsRight
          case _ => fail
        }
        case trees.SubString(string, from, to) => template match {
          case SubstringOperation(templateString, templateFrom, templateTo) => for {
            mappingsString <- extract(string, templateString)
            mappingsFrom <- extract(from, templateFrom)
            mappingsTo <- extract(to, templateTo)
          } yield mappingsString ++ mappingsFrom ++ mappingsTo
          case _ => fail
        }
        case trees.StringLength(string) => template match {
          case PrimitiveFunction(bi.StringLength, _, Seq(templateString), None) => extract(string, templateString)
          case _ => fail
        }
        case trees.Plus(left, right) => template match {
          case Operation("+", Seq(templateLeft, templateRight)) => for {
            mappingsLeft <- extract(left, templateLeft)
            mappingsRight <- extract(right, templateRight)
          } yield mappingsLeft ++ mappingsRight
          case _ => fail
        }
        case trees.Minus(left, right) => template match {
          case Operation("-", Seq(templateLeft, templateRight)) => for {
            mappingsLeft <- extract(left, templateLeft)
            mappingsRight <- extract(right, templateRight)
          } yield mappingsLeft ++ mappingsRight
          case _ => fail
        }
        case trees.Times(left, right) => template match {
          case Operation("*", Seq(templateLeft, templateRight)) => for {
            mappingsLeft <- extract(left, templateLeft)
            mappingsRight <- extract(right, templateRight)
          } yield mappingsLeft ++ mappingsRight
          case _ => fail
        }
        case trees.Division(left, right) => template match {
          case Operation("/", Seq(templateLeft, templateRight)) => for {
            mappingsLeft <- extract(left, templateLeft)
            mappingsRight <- extract(right, templateRight)
          } yield mappingsLeft ++ mappingsRight
          case _ => fail
        }
        case trees.UMinus(inner) => template match {
          case Operation("-", Seq(templateInner)) => extract(inner, templateInner)
          case _ => fail
        }
        case _ => fail
      }
    }
  }
}