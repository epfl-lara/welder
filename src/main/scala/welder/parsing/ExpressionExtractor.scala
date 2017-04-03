package welder
package parsing

import scala.language.implicitConversions

trait ExpressionExtractors { self: Interpolator =>

  trait ExpressionExtractor extends Extractor { self: ExprIR.type => 

    import program.trees
    import program.symbols


    private case class State(local: Store, global: Store)

    private object State {
      def empty: State = State(Store.empty, Store.empty)
    }

    private sealed abstract class MatchObligation
    private case class ExprMatch(expr: trees.Expr, template: Expression) extends MatchObligation
    private case class TypeMatch(tpe: trees.Type, template: Type) extends MatchObligation
    private case class OptTypeMatch(tpe: trees.Type, optTemplate: Option[Type]) extends MatchObligation
    private case class MultipleObligations(pairs: Seq[MatchObligation]) extends MatchObligation
    private case class WithBindings(bindings: Seq[(inox.Identifier, String)], obligation: MatchObligation) extends MatchObligation

    private def withBindings(bindings: Seq[(inox.Identifier, String)])(obligation: MatchObligation): MatchObligation = WithBindings(bindings, obligation)
    private def withBinding(id: inox.Identifier, name: String)(obligation: MatchObligation): MatchObligation = WithBindings(Seq((id, name)), obligation)

    private implicit def toExprObligation(pair: (trees.Expr, Expression)): MatchObligation = ExprMatch(pair._1, pair._2)
    private implicit def toTypeObligation(pair: (trees.Type, Type)): MatchObligation = TypeMatch(pair._1, pair._2)
    private implicit def toOptTypeObligation(pair: (trees.Type, Option[Type])): MatchObligation = OptTypeMatch(pair._1, pair._2)
    private implicit def toExprObligations(pairs: Seq[(trees.Expr, Expression)]): MatchObligation = MultipleObligations(pairs.map(toExprObligation(_)))
    private implicit def toTypeObligations(pairs: Seq[(trees.Type, Type)]): MatchObligation = MultipleObligations(pairs.map(toTypeObligation(_)))
    private implicit def toOptTypeObligations(pairs: Seq[(trees.Type, Option[Type])]): MatchObligation = MultipleObligations(pairs.map(toOptTypeObligation(_)))

    private def extract(pairs: MatchObligation*)(implicit state: State): Option[(Store, Match)] = {

      val zero: Option[(Store, Match)] = Some((state.global, empty))

      pairs.foldLeft(zero) {
        case (None, _) => None
        case (Some((globalAcc, matchingsAcc)), pair) => {

          val optNewGlobalAndMatchings = pair match {

            case ExprMatch(expr, template) => 
              extractOne(expr, template)(State(state.local, globalAcc))

            case TypeMatch(tpe, template) => 
              TypeIR.extract(tpe, template).map((globalAcc, _))

            case OptTypeMatch(tpe, None) => Some((globalAcc, empty))

            case OptTypeMatch(tpe, Some(template)) => TypeIR.extract(tpe, template).map((globalAcc, _))

            case MultipleObligations(pairs) => extract(pairs : _*)

            case WithBindings(bindings, matchPair) => {
              val newLocal = bindings.foldLeft(state.local) {
                case (currentStore, (id, name)) => currentStore.add(id, name)
              }

              extract(matchPair)(State(newLocal, globalAcc))
            }
          }

          optNewGlobalAndMatchings map {
            case (newGlobal, extraMatchings) => (newGlobal, matchingsAcc ++ extraMatchings)
          }
        }
      }
    }

    private class Store(val inoxToIr: Map[inox.Identifier, String], val irToInox: Map[String, inox.Identifier]) {

      override def toString = inoxToIr.toString + "\n" + irToInox.toString

      def get(id: inox.Identifier): Option[String] = inoxToIr.get(id)
      def get(name: String): Option[inox.Identifier] = irToInox.get(name)

      def add(id: inox.Identifier, name: String): Store = {

        val optOldName = inoxToIr.get(id)
        val optOldId = irToInox.get(name)

        val newIrToInox = optOldName match {
          case None => irToInox + ((name -> id))
          case Some(oldName) => irToInox - oldName + ((name -> id))
        }

        val newInoxToIR = optOldId match {
          case None => inoxToIr + ((id -> name))
          case Some(oldId) => inoxToIr - oldId + ((id -> name))
        }
        
        new Store(newInoxToIR, newIrToInox)
      }
    }

    private object Store {
      val empty = new Store(Map(), Map())
    }

    def extract(expr: trees.Expr, template: Expression): Option[Match] = extract(expr -> template)(State.empty).map(_._2)

    private def extractOne(expr: trees.Expr, template: Expression)(implicit state: State): Option[(Store, Match)] = {

      val store = state.global
      val success = Some((store, empty))

      template match {
        case Hole(index) =>
          return Some((store, Map(index -> expr)))
        case TypeAnnotationOperation(templateInner, templateType) =>
          return extract(expr.getType -> templateType, expr -> templateInner)
        case _ => ()
      }

      expr match {

        // Variables

        case trees.Variable(inoxId, _, _) => template match {
          case Variable(id) => {
            val name = id.getName
            (state.local.get(name), state.local.get(inoxId)) match {
              case (Some(`inoxId`), Some(`name`)) => success  // Locally bound identifier.
              case (None, None) => (store.get(name), store.get(inoxId)) match {
                case (Some(`inoxId`), Some(`name`)) => success  // Globally bound identifier.
                case (None, None) => Some((store.add(inoxId, name), empty)) // Free identifier. We recorder it in the global store.
                case _ => fail
              }
              case _ => fail
            }
          }
          case _ => fail
        }

        // Control structures.

        case trees.IfExpr(cond, thenn, elze) => template match {
          case Operation("IfThenElse", Seq(templateCond, templateThenn, templateElze)) =>
            extract(cond -> templateCond, thenn -> templateThenn, elze -> templateElze)
          case _ => fail
        }

        case trees.Assume(pred, body) => template match {
          case Operation("Assume", Seq(templatePred, templateBody)) =>
            extract(pred -> templatePred, body -> templateBody)
          case _ => fail
        }

        case trees.Let(vd, value, body) => template match {
          case Let(Seq((templateId, optTemplateType, templateValue), rest @ _*), templateBody) => {

            val templateRest = rest match {
              case Seq() => templateBody
              case _ => Let(rest, templateBody)
            }

            extract(value -> templateValue, vd.tpe -> optTemplateType, withBinding(vd.id, templateId.getName)(body -> templateRest))
          }
          case _ => fail
        }

        case trees.Lambda(args, body) => template match {
          case Abstraction(Lambda, templateArgs, templateBody) if (args.length == templateArgs.length) =>
            extract(
              args.map(_.tpe).zip(templateArgs.map(_._2)), 
              withBindings(args.map(_.id).zip(templateArgs.map(_._1.getName)))(body -> templateBody))
          case _ => fail
        }

        case trees.Forall(args, body) => template match {
          case Abstraction(Forall, templateArgs, templateBody) if (args.length == templateArgs.length) =>
            extract(
              args.map(_.tpe).zip(templateArgs.map(_._2)), 
              withBindings(args.map(_.id).zip(templateArgs.map(_._1.getName)))(body -> templateBody))
          case _ => fail
        }

        case trees.Choose(arg, pred) => template match {
          case Abstraction(Choose, Seq((id, optTemplateType), rest @ _*), templatePred) => {
            val templateRest = rest match {
              case Seq() => templatePred
              case _ => Abstraction(Choose, rest, templatePred)
            }

            extract(arg.tpe -> optTemplateType, withBinding(arg.id, id.getName)(pred -> templateRest))
          }
          case _ => fail
        }

        // Functions.

        case trees.Application(callee, args) => template match {
          case Application(templateCallee, templateArgs) if (args.length == templateArgs.length) =>
            extract(callee -> templateCallee, args.zip(templateArgs))
          case _ => fail
        }

        case trees.FunctionInvocation(id, tpes, args) => template match {
          case Application(TypedFunDef(fd, optTemplatesTypes), templateArgs) if (id == fd.id && args.length == templateArgs.length) => {
            optTemplatesTypes match {
              case None => extract(args.zip(templateArgs))
              case Some(templateTypes) if (tpes.length == templateTypes.length) => extract(args.zip(templateArgs), tpes.zip(templateTypes))
              case _ => fail
            }
          }
          case _ => fail
        }

        // ADTs.

        case trees.ADT(trees.ADTType(id, tpes), args) => template match {
          case Application(TypedConsDef(cons, optTemplatesTypes), templateArgs) if (id == cons.id && args.length == templateArgs.length) => {
            optTemplatesTypes match {
              case None => extract(args.zip(templateArgs))
              case Some(templateTypes) if (tpes.length == templateTypes.length) => extract(args.zip(templateArgs), tpes.zip(templateTypes))
              case _ => fail
            }
          }
          case _ => fail
        }

        case trees.ADTSelector(adt, selector) => template match {
          case Selection(adtTemplate, Field((cons, vd))) if (vd.id == selector) =>  // TODO: Handle selectors with the same name.
            extract(adt -> adtTemplate)
          case _ => fail
        }

        // Instance checking and casting.

        case trees.AsInstanceOf(inner, tpe) => template match {
          case AsInstanceOfOperation(templateInner, templateType) =>
            extract(inner -> templateInner, tpe -> templateType)
          case _ => fail
        }

        case trees.IsInstanceOf(inner, tpe) => template match {
          case IsInstanceOfOperation(templateInner, templateType) =>
            extract(inner -> templateInner, tpe -> templateType)
          case _ => fail
        }

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
          case Operation("!", Seq(templateInner)) => extract(inner -> templateInner)
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
          case StringLengthOperation(templateString) => extract(string -> templateString)
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
          case Operation("-", Seq(templateInner)) => extract(inner -> templateInner)
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
          case Operation("~", Seq(templateInner)) => extract(inner -> templateInner)
          case _ => fail
        }

        case trees.BVOr(left, right) => template match {
          case Operation("|", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
        }

        case trees.BVAnd(left, right) => template match {
          case Operation("&", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        case trees.BVXor(left, right) => template match {
          case Operation("^", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        case trees.BVShiftLeft(left, right) => template match {
          case Operation("<<", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        case trees.BVAShiftRight(left, right) => template match {
          case Operation(">>", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        case trees.BVLShiftRight(left, right) => template match {
          case Operation(">>>", Seq(templateLeft, templateRight)) =>
            extract(left -> templateLeft, right -> templateRight)
          case _ => fail
        }

        // Tuples.

        case trees.Tuple(exprs) => template match {
          case Operation("Tuple", templates) if (exprs.length == templates.length) =>
            extract(exprs.zip(templates))
          case _ => fail
        }

        case trees.TupleSelect(inner, index) => template match {
          case Selection(templateInner, TupleField(`index`)) => extract(inner -> templateInner)
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

        // Bags.

        case trees.FiniteBag(mappings, tpe) => template match {
          case BagConstruction(Bindings(Seq(), templateMappings), optTemplateType) if (mappings.length == templateMappings.length) => {
            val (keys, values) = mappings.unzip
            val (templatesKeys, templatesValues) = templateMappings.unzip

            extract(keys.zip(templatesKeys), values.zip(templatesValues), tpe -> optTemplateType)
          }
          case _ => fail
        }

        case trees.BagAdd(bag, element) => (bag.getType(symbols), template) match {
          case (trees.BagType(tpe), BagAddOperation(templateBag, templateElement, optTemplateType)) =>
            extract(bag -> templateBag, element -> templateElement, tpe -> optTemplateType)
          case _ => fail
        }

        case trees.MultiplicityInBag(element, bag) => (bag.getType, template) match {
          case (trees.BagType(tpe), BagMultiplicityOperation(templateBag, templateElement, optTemplateType)) =>
            extract(element -> templateElement, bag -> templateBag, tpe -> optTemplateType)
          case _ => fail
        }

        case trees.BagIntersection(left, right) => (left.getType, template) match {
          case (trees.BagType(tpe), BagIntersectionOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(left -> templateLeft, right -> templateRight, tpe -> optTemplateType)
          case _ => fail
        }

        case trees.BagUnion(left, right) => (left.getType, template) match {
          case (trees.BagType(tpe), BagUnionOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(left -> templateLeft, right -> templateRight, tpe -> optTemplateType)
          case _ => fail
        }

        case trees.BagDifference(left, right) => (left.getType, template) match {
          case (trees.BagType(tpe), BagDifferenceOperation(templateLeft, templateRight, optTemplateType)) =>
            extract(left -> templateLeft, right -> templateRight, tpe -> optTemplateType)
          case _ => fail
        }

        // Maps.

        case trees.FiniteMap(pairs, default, keyType, valueType) => template match {
          case MapConstruction(templateDefault, Bindings(Seq(), templatesPairs), optTemplatesTypes) if (pairs.length == templatesPairs.length) => {

            val (optTemplateKeyType, optTemplateValueType) = optTemplatesTypes match {
              case Some(Right((k, v))) => (Some(k), Some(v))
              case Some(Left(k)) => (Some(k), None)
              case None => (None, None) 
            }

            val (keys, values) = pairs.unzip
            val (templatesKeys, templatesValues) = templatesPairs.unzip

            extract(keys.zip(templatesKeys), values.zip(templatesValues), keyType -> optTemplateKeyType, valueType -> optTemplateValueType, default -> templateDefault)
          }
          case _ => fail
        }

        case trees.MapApply(map, key) => (map.getType, template) match {
          case (trees.MapType(keyType, valueType), MapApplyOperation(templateMap, templateKey, optTemplatesTypes)) => {
            val (optTemplateKeyType, optTemplateValueType) = optTemplatesTypes match {
              case Some((k, v)) => (Some(k), Some(v))
              case None => (None, None)
            }

            extract(map -> templateMap, key -> templateKey, keyType -> optTemplateKeyType, valueType -> optTemplateValueType)
          }
          case _ => fail
        }

        case trees.MapUpdated(map, key, value) => (map.getType, template) match {
          case (trees.MapType(keyType, valueType), MapUpdatedOperation(templateMap, templateKey, templateValue, optTemplatesTypes)) => {
            val (optTemplateKeyType, optTemplateValueType) = optTemplatesTypes match {
              case Some((k, v)) => (Some(k), Some(v))
              case None => (None, None)
            }

            extract(map -> templateMap, key -> templateKey, keyType -> optTemplateKeyType, value -> templateValue, valueType -> optTemplateValueType)
          }
          case _ => fail
        }

        case _ => fail
      }
    }
  }
}