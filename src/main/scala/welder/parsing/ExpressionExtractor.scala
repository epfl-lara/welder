package welder
package parsing

import scala.language.implicitConversions

trait ExpressionExtractors { self: Interpolator =>

  trait ExpressionExtractor extends Extractor { self: ExprIR.type => 

    import program.trees
    import program.symbols

    private sealed abstract class MatchPair
    private case class ExprPair(pair: (trees.Expr, Expression)) extends MatchPair
    private case class TypePair(pair: (trees.Type, Type)) extends MatchPair
    private case class OptTypePair(pair: (trees.Type, Option[Type])) extends MatchPair
    private case class SeqPairs(pairs: Seq[MatchPair]) extends MatchPair

    private implicit def toExprPair(pair: (trees.Expr, Expression)): MatchPair = ExprPair(pair)
    private implicit def toTypePair(pair: (trees.Type, Type)): MatchPair = TypePair(pair)
    private implicit def toOptTypePair(pair: (trees.Type, Option[Type])): MatchPair = OptTypePair(pair)
    private implicit def toExprPairSeq(pairs: Seq[(trees.Expr, Expression)]): MatchPair = SeqPairs(pairs.map(ExprPair(_)))
    private implicit def toTypePairSeq(pairs: Seq[(trees.Type, Type)]): MatchPair = SeqPairs(pairs.map(TypePair(_)))
    private implicit def toOptTypePairSeq(pairs: Seq[(trees.Type, Option[Type])]): MatchPair = SeqPairs(pairs.map(OptTypePair(_)))

    private def extract(pairs: MatchPair*)(implicit store: Map[String, inox.Identifier]): Option[Match] = {
      Utils.traverse(pairs.map({
        case ExprPair((expr, template)) => extract(expr, template)
        case TypePair((tpe, template)) => TypeIR.extract(tpe, template)
        case OptTypePair((tpe, None)) => success
        case OptTypePair((tpe, Some(template))) => TypeIR.extract(tpe, template)
        case SeqPairs(pairs) => extract(pairs : _*)
      })).map(_.fold(empty)(_ ++ _))
    }

    def extract(expr: trees.Expr, template: Expression)(implicit store: Map[String, inox.Identifier]): Option[Match] = {

      template match {
        case Hole(index) =>
          return Some(Map(index -> expr))
        case TypeApplication(Operation("TypeAnnotation", Seq(templateInner)), Seq(templateType)) =>
          return extract(expr.getType -> templateType, expr -> templateInner)
        case _ => ()
      }

      expr match {

        // Various.

        case trees.CharLiteral(char) => template match {
          case Literal(CharLiteral(`char`)) => success
          case _ => fail 
        }

        case trees.UnitLiteral() => template match {
          case Literal(UnitLiteral) => success
          case _ => fail
        }

        case trees.Equals(left, right) => template match {
          case Operation("==", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        // Booleans.

        case trees.BooleanLiteral(bool) => template match {
          case Literal(BooleanLiteral(`bool`)) => success
          case _ => fail
        }
        
        case trees.And(exprs) => template match {
          case Operation("&&", templates) if (exprs.length == templates.length) =>
            extract(exprs.zip(templates))
          case _ => fail
        }

        case trees.Or(exprs) => template match {
          case Operation("||", templates) if (exprs.length == templates.length) =>
            extract(exprs.zip(templates))
          case _ => fail
        }

        case trees.Implies(left, right) => template match {
          case Operation("==>", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        case trees.Not(inner) => template match {
          case Operation("!", Seq(templateInner)) => extract(inner, templateInner)
          case _ => fail
        }

        // Strings.

        case trees.StringLiteral(string) => template match {
          case Literal(StringLiteral(`string`)) => success
          case _ => fail
        }

        case trees.StringConcat(left, right) => template match {
          case ConcatenateOperation(templateLeft, templateRight) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        case trees.SubString(string, from, to) => template match {
          case SubstringOperation(templateString, templateFrom, templateTo) =>
            extract(string -> templateString, from -> templateFrom, to -> templateTo)
          case _ => fail
        }

        case trees.StringLength(string) => template match {
          case StringLengthOperation(templateString) => extract(string, templateString)
          case _ => fail
        }

        // Numbers.

        case trees.IntegerLiteral(value) => template match {
          case Literal(NumericLiteral(string)) if (scala.util.Try(BigInt(string)).toOption == Some(value)) => success
          case _ => fail
        }

        case trees.FractionLiteral(numerator, denominator) => template match {
          case Literal(NumericLiteral(string)) if { val (n, d) = Utils.toFraction(string); n * denominator == d * numerator } => success
          case _ => fail
        }

        case trees.Plus(left, right) => template match {
          case Operation("+", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.Minus(left, right) => template match {
          case Operation("-", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.Times(left, right) => template match {
          case Operation("*", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.Division(left, right) => template match {
          case Operation("/", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.UMinus(inner) => template match {
          case Operation("-", Seq(templateInner)) => extract(inner, templateInner)
          case _ => fail
        }
        case trees.Remainder(left, right) => template match {
          case Operation("%", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.Modulo(left, right) => template match {
          case Operation("mod", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.LessThan(left, right) => template match {
          case Operation("<", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.GreaterThan(left, right) => template match {
          case Operation(">", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.LessEquals(left, right) => template match {
          case Operation("<=", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }
        case trees.GreaterEquals(left, right) => template match {
          case Operation(">=", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        // Bit vectors.

        case trees.BVLiteral(value, _) => template match {
          case Literal(NumericLiteral(string)) if (scala.util.Try(BigInt(string)).toOption == Some(value)) => success
          case _ => fail
        }

        case trees.BVNot(inner) => template match {
          case Operation("~", Seq(templateInner)) => extract(inner, templateInner)
          case _ => fail
        }

        // Sets.

        case trees.FiniteSet(elements, tpe) => template match {
          case SetConstruction(templatesElements, optTemplateType) if (elements.length == templatesElements.length) =>
            extract(elements.zip(templatesElements), tpe -> optTemplateType)
          case _ => fail
        }

        case trees.SetAdd(set, element) => (set.getType(symbols), template) match {
          case (trees.SetType(tpe), SetAddOperation(templateSet, templateElement, optTemplateType)) =>
            extract(set -> templateSet, element -> templateElement, tpe -> optTemplateType)
          case _ => fail
        }

        case trees.ElementOfSet(element, set) => (set.getType(symbols), template) match {
          case (trees.SetType(tpe), ContainsOperation(templateSet, templateElement, optTemplateType)) =>
            extract(set -> templateSet, element -> templateElement, tpe -> optTemplateType)
          case _ => fail
        }

        case trees.SubsetOf(left, right) => (left.getType(symbols), template) match {
          case (trees.SetType(tpe), SubsetOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(left -> templateLeft, right -> templateRight, tpe -> optTemplateType)
          case _ => fail
        }

        case trees.SetIntersection(left, right) => (left.getType(symbols), template) match {
          case (trees.SetType(tpe), SetIntersectionOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(left -> templateLeft, right -> templateRight, tpe -> optTemplateType)
          case _ => fail
        }

        case trees.SetDifference(left, right) => (left.getType(symbols), template) match {
          case (trees.SetType(tpe), SetDifferenceOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(left -> templateLeft, right -> templateRight, tpe -> optTemplateType)
          case _ => fail
        }

        case _ => fail
      }
    }
  }
}