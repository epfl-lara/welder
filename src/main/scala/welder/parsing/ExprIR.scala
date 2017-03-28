package welder
package parsing

import inox._

import scala.util.parsing.input._

/** IR for expressions. */
class ExprIR(val program: InoxProgram) extends IR {

  import program.trees
  import program.symbols

  val bi = new DefaultBuiltIns {}

  val solver = new SimpleConstraintSolver(program)
  import solver.constraints._

  sealed abstract class Identifier extends Positional {
    def getName: String
    def getShortName: String

    override def toString = pos + "@" + getName
  }
  case class IdentifierName(name: String) extends Identifier {
    override def getName = name
    override def getShortName = name
  }
  case class IdentifierIdentifier(identifier: inox.Identifier) extends Identifier {
    override def getName = identifier.uniqueName
    override def getShortName = identifier.toString
  }

  type Operator = String
  
  sealed abstract class Field extends Positional
  case class FieldName(name: String) extends Field
  case class FieldIdentifier(identifier: inox.Identifier) extends Field

  type Type = trees.Type

  sealed abstract class Value
  case class EmbeddedExpr(expr: trees.Expr) extends Value
  case class EmbeddedValue(value: Any) extends Value
  case class EmbeddedIdentifier(identifier: inox.Identifier) extends Value
  case class Name(name: String) extends Value
  case class NumericLiteral(value: String) extends Value
  case class StringLiteral(string: String) extends Value
  case class BooleanLiteral(value: Boolean) extends Value
  case class CharLiteral(value: Char) extends Value
  case object UnitLiteral extends Value

  sealed abstract class Quantifier
  case object Lambda extends Quantifier
  case object Forall extends Quantifier
  case object Exists extends Quantifier
  case object Choose extends Quantifier

  //---- Extractors ----//

  object TupleField {
    def unapply(field: Field): Option[Int] = field match {
      case FieldName(name) if name.startsWith("_") => scala.util.Try(name.tail.toInt).toOption.filter(_ >= 1)
      case _ => None 
    }
  }

  object Field {

    lazy val allFields = symbols.adts.toSeq.flatMap({
      case (_, c: trees.ADTConstructor) => c.fields.map((vd: trees.ValDef) => (c, vd))
      case _ => Seq()
    })

    lazy val fieldsById = allFields.groupBy(_._2.id)
    lazy val fieldsByName = allFields.groupBy(_._2.id.name)

    def unapplySeq(field: Field): Option[Seq[(trees.ADTConstructor, trees.ValDef)]] = field match {
      case FieldName(name) => fieldsByName.get(name)
      case FieldIdentifier(id) => fieldsById.get(id)
      case _ => None
    }
  }

  object FunDef {

    lazy val functionsByName = symbols.functions.toSeq.map(_._2).groupBy(_.id.name)

    def unapplySeq(expression: Expression): Option[Seq[trees.FunDef]] = expression match {
      case Literal(EmbeddedIdentifier(identifier)) => symbols.functions.get(identifier).map(Seq(_))
      case Literal(Name(string)) => functionsByName.get(string)
      case _ => None
    }
  }

  object TypedFunDef {
    def unapply(expression: Expression): Option[(trees.FunDef, Option[Seq[trees.Type]])] = expression match {
      case TypeApplication(FunDef(fd), targs) => Some((fd, Some(targs)))
      case FunDef(fd) => Some((fd, None))
      case _ => None
    }
  }

  object ConsDef {

    lazy val allConstructors = symbols.adts.toSeq.flatMap({
      case (_, c: trees.ADTConstructor) => Some(c)
      case _ => None
    })

    lazy val consById = allConstructors.groupBy(_.id)
    lazy val consByName = allConstructors.groupBy(_.id.name)

    def unapplySeq(expression: Expression): Option[Seq[trees.ADTConstructor]] = expression match {
      case Literal(EmbeddedIdentifier(identifier)) => consById.get(identifier)
      case Literal(Name(string)) => consByName.get(string)
      case _ => None
    }
  }

  object TypedConsDef {
    def unapply(expression: Expression): Option[(trees.ADTConstructor, Option[Seq[trees.Type]])] = expression match {
      case TypeApplication(ConsDef(cons), targs) => Some((cons, Some(targs)))
      case ConsDef(cons) => Some((cons, None))
      case _ => None
    }
  }

  object NumericBinOp {
    def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
      case "+" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Plus(lhs, rhs) })
      case "-" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Minus(lhs, rhs) })
      case "*" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Times(lhs, rhs) })
      case "/" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Division(lhs, rhs) })
      case _ => None
    }
  }

  object IntegralBinOp {
    def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
      case "%" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Remainder(lhs, rhs) })
      case "mod" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Modulo(lhs, rhs) })
      case _ => None
    }
  }

  object ComparableBinOp {
    def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
      case "<=" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.LessEquals(lhs, rhs) })
      case "<" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.LessThan(lhs, rhs) })
      case ">=" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.GreaterEquals(lhs, rhs) })
      case ">" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.GreaterThan(lhs, rhs) })
      case _ => None
    }
  }

  object BooleanBinOp {
    def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
      case "==>" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Implies(lhs, rhs) })
      case "&&" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.And(lhs, rhs) })
      case "||" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.Or(lhs, rhs) })
      case _ => None
    }
  }

  object BitVectorBinOp {
    def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
      case "|" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVOr(lhs, rhs) })
      case "&" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVAnd(lhs, rhs) })
      case "^" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVXor(lhs, rhs) })
      case "<<" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVShiftLeft(lhs, rhs) })
      case ">>" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVAShiftRight(lhs, rhs) })
      case ">>>" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.BVLShiftRight(lhs, rhs) })
      case _ => None
    }
  }

  object SetConstruction {
    def unapply(expr: Expression): Option[(Seq[Expression], Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.SetConstructor))), Seq(tpe)), es) => 
        Some((es, Some(tpe)))
      case Application(Literal(Name(bi.BuiltIn(bi.SetConstructor))), es) => 
        Some((es, None))
      case Operation("Set", es) => 
        Some((es, None))
      case _ => None
    }
  }

  object SetBinaryOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, (trees.Expr, trees.Expr) => trees.Expr, Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(SetBinFun(f))), Seq(tpe)), Seq(set1, set2)) => Some((set1, set2, f, Some(tpe)))
      case Application(Literal(Name(SetBinFun(f))), Seq(set1, set2)) => Some((set1, set2, f, None))
      case Operation(SetBinOp(f), Seq(set1, set2)) => Some((set1, set2, f, None))
      case _ => None
    }

    object SetBinOp {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case "∪" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetUnion(lhs, rhs) })
        case "∩" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetIntersection(lhs, rhs) })
        case "∖" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetDifference(lhs, rhs) })
        case _ => None
      }
    }

    object SetBinFun {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case bi.BuiltIn(bi.SetUnion) => 
          Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetUnion(lhs, rhs) })
        case bi.BuiltIn(bi.SetIntersection) =>
          Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetIntersection(lhs, rhs) })
        case bi.BuiltIn(bi.SetDifference) =>
          Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetDifference(lhs, rhs) })
        case _ => None
      }
    }
  }

  object SubsetOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.SetSubset))), Seq(tpe)), Seq(set1, set2)) =>
        Some((set1, set2, Some(tpe)))
      case Application(Literal(Name(bi.BuiltIn(bi.SetSubset))), Seq(set1, set2)) =>
        Some((set1, set2, None))
      case Operation("⊆", Seq(set1, set2)) =>
        Some((set1, set2, None))
      case _ => None
    }
  }

  object ContainsOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.SetContains))), Seq(tpe)), Seq(set, elem)) =>
        Some((set, elem, Some(tpe)))
      case Application(Literal(Name(bi.BuiltIn(bi.SetContains))), Seq(set, elem)) =>
        Some((set, elem, None))
      case Operation("∈", Seq(elem, set)) =>
        Some((set, elem, None))
      case _ => None
    }
  }

  object SetAddOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.SetAdd))), Seq(tpe)), Seq(set, elem)) =>
        Some((set, elem, Some(tpe)))
      case Application(Literal(Name(bi.BuiltIn(bi.SetAdd))), Seq(set, elem)) =>
        Some((set, elem, None))
      case _ => None
    }
  }

  object ConcatenateOperation {
    def unapply(expr: Expression): Option[(Expression, Expression)] = expr match {
      case Application(Literal(Name(bi.BuiltIn(bi.StringConcatenate))), Seq(str1, str2)) =>
        Some((str1, str2))
      case Operation("++", Seq(str1, str2)) =>
        Some((str1, str2))
      case _ => None
    }
  }

  object SubstringOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, Expression)] = expr match {
      case Application(Literal(Name(bi.BuiltIn(bi.StringSubstring))), Seq(str, start, end)) =>
        Some((str, start, end))
      case _ => None
    }
  }

  object Binding {
    def unapply(expr: Expression): Option[(Expression, Expression)] = expr match {
      case Operation("->", Seq(a, b)) => Some((a, b))
      case _ => None
    }

    def getAll(es: Seq[Expression]): Option[Seq[(Expression, Expression)]] = {
      val bs = es.collect({
        case Binding(a, b) => (a, b)
      })

      if (bs.length == es.length) {
        Some(bs)
      }
      else {
        None
      }
    }
  }

  object BagConstruction {
    def unapply(expr: Expression): Option[(Seq[(Expression, Expression)], Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.BagConstructor))), Seq(tpe)), es) => 
        Binding.getAll(es).map((_, Some(tpe)))
      case Application(Literal(Name(bi.BuiltIn(bi.BagConstructor))), es) => 
        Binding.getAll(es).map((_, None))
      case Operation("Set", es) => 
        Binding.getAll(es).map((_, None))
      case _ => None
    }
  }

  object BagMultiplicityOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.BagMultiplicity))), Seq(tpe)), Seq(m, k)) => 
        Some((m, k, Some(tpe)))
      case Application(Literal(Name(bi.BuiltIn(bi.BagMultiplicity))), Seq(m, k)) => 
        Some((m, k, None))
      case _ => None
    }
  }

  object BagAddOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.BagAdd))), Seq(tpe)), Seq(bag, elem)) =>
        Some((bag, elem, Some(tpe)))
      case Application(Literal(Name(bi.BuiltIn(bi.BagAdd))), Seq(bag, elem)) =>
        Some((bag, elem, None))
      case _ => None
    }
  }

  object BagBinaryOperation {

    def unapply(expr: Expression): Option[(Expression, Expression, (trees.Expr, trees.Expr) => trees.Expr, Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(BagBinFun(f))), Seq(tpe)), Seq(map1, map2)) =>
        Some((map1, map2, f, Some(tpe)))
      case Application(Literal(Name(BagBinFun(f))), Seq(map1, map2)) =>
        Some((map1, map2, f, None))
      case _ => None
    }

    object BagBinFun {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case bi.BuiltIn(bi.BagUnion) => Some((map1: trees.Expr, map2: trees.Expr) => trees.BagUnion(map1, map2))
        case bi.BuiltIn(bi.BagIntersection) => Some((map1: trees.Expr, map2: trees.Expr) => trees.BagIntersection(map1, map2))
        case bi.BuiltIn(bi.BagDifference) => Some((map1: trees.Expr, map2: trees.Expr) => trees.BagDifference(map1, map2))
        case _ => None
      }
    }
  }

  object MapConstruction {
    def unapply(expr: Expression): Option[(Expression, Seq[(Expression, Expression)], Option[Type], Option[Type])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.MapConstructor))), Seq(tpe1, tpe2)), Seq(e, es @ _*)) => 
        Binding.getAll(es).map((e, _, Some(tpe1), Some(tpe2)))
      case Application(Literal(Name(bi.BuiltIn(bi.MapConstructor))), Seq(e, es @ _*)) => 
        Binding.getAll(es).map((e, _, None, None))
      case TypeApplication(Operation("Map", Seq(e, es @ _*)), Seq(t)) => 
        Binding.getAll(es).map((e, _, Some(t), None))
      case Operation("Map", Seq(e, es @ _*)) => 
        Binding.getAll(es).map((e, _, None, None))
      case _ => None
    }
  }

  object MapApplyOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, Option[(Type, Type)])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.MapApply))), Seq(tpe1, tpe2)), Seq(map, elem)) =>
        Some((map, elem, Some((tpe1, tpe2))))
      case Application(Literal(Name(bi.BuiltIn(bi.MapApply))), Seq(map, elem)) =>
        Some((map, elem, None))
      case _ => None
    }
  }

  object MapUpdatedOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, Expression, Option[(Type, Type)])] = expr match {
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.MapUpdated))), Seq(tpe1, tpe2)), Seq(map, key, value)) =>
        Some((map, key, value, Some((tpe1, tpe2))))
      case Application(TypeApplication(Literal(Name(bi.BuiltIn(bi.MapUpdated))), Seq(tpe1, tpe2)), Seq(map, Binding(key, value))) =>
        Some((map, key, value, Some((tpe1, tpe2))))
      case Application(Literal(Name(bi.BuiltIn(bi.MapUpdated))), Seq(map, key, value)) =>
        Some((map, key, value, None))
      case Application(Literal(Name(bi.BuiltIn(bi.MapUpdated))), Seq(map, Binding(key, value))) =>
        Some((map, key, value, None))
      case _ => None
    }
  }

  /** Conversion to Inox expression. */
  def toInoxExpr(expr: Expression): trees.Expr = {
    typeCheck(expr, Unknown.fresh(expr.pos))(Map()) match {
      case Unsatifiable(es) => throw new Exception(es.map(_.toString).mkString("\n\n"))
      case WithConstraints(elaborator, constraints) => {
        val unifier = solver.solveConstraints(constraints)
        elaborator(unifier)
      }
    }
  }

  /** Type inference and expression elaboration.
   *
   * @param expr     The expression to typecheck.
   * @param expected The type the expression is expected to have.
   * @param store    Mappings of variables.
   * @return A sequence of constraints and a way to build an Inox expression given a solution to the constraints.
   */
  def typeCheck(expr: Expression, expected: Unknown)
               (implicit store: Map[String, (inox.Identifier, trees.Type)]): Constrained[trees.Expr] = {
    implicit val position: Position = expr.pos

    expr match {

      //---- Literals ----//

      // Boolean literals.
      case Literal(BooleanLiteral(value)) => Constrained.pure({
        trees.BooleanLiteral(value)
      }).addConstraint({
        Constraint.equal(expected, trees.BooleanType)
      })

      // Unit literal.
      case Literal(UnitLiteral) => Constrained.pure({
        trees.UnitLiteral()
      }).addConstraint({
        Constraint.equal(expected, trees.UnitType)
      })

      // String literal.
      case Literal(StringLiteral(string)) => Constrained.pure({
        trees.StringLiteral(string)
      }).addConstraint({
        Constraint.equal(expected, trees.StringType)
      })

      // Char literal.
      case Literal(CharLiteral(character)) => Constrained.pure({
        trees.CharLiteral(character)
      }).addConstraint({
        Constraint.equal(expected, trees.CharType)
      })

      // Numeric literal.
      case Literal(NumericLiteral(string)) => Constrained.withUnifier({ (unifier: Unifier) =>

        unifier(expected) match {
          case trees.IntegerType => trees.IntegerLiteral(BigInt(string))
          case trees.Int32Type => trees.IntLiteral(string.toInt)
          case trees.BVType(n) => trees.BVLiteral(BigInt(string), n)
          case trees.RealType => {
            val (n, d) = Utils.toFraction(string)
            trees.FractionLiteral(n, d)
          }
          case tpe => throw new Exception("typeCheck: Unexpected type during elaboration: " + tpe)
        }
      }).addConstraint(if (string.contains(".")) {
        Constraint.equal(expected, trees.RealType)
      } else {
        Constraint.isNumeric(expected)
      })

      //---- Variables ----//

      // Embedded identifier.
      case Literal(EmbeddedIdentifier(i)) => Constrained.withUnifier({ (unifier: Unifier) =>
        val (_, t) = store(i.uniqueName)
        trees.Variable(i, unifier(t), Set.empty)
      }).checkImmediate(
        store.contains(i.uniqueName), "Unknown identifier " + i + ".", expr.pos
      ).addConstraint({
        Constraint.equal(store(i.uniqueName)._2, expected)
      })

      // Variable.
      case Variable(variable) => Constrained.withUnifier({ (unifier: Unifier) =>
        val (i, t) = store(variable.getName)
        trees.Variable(i, unifier(t), Set.empty)
      }).checkImmediate(
        store.contains(variable.getName), "Unknown variable " + variable.getShortName + ".", expr.pos
      ).addConstraint({
        Constraint.equal(store(variable.getName)._2, expected)
      })

      //---- Embedded values ----//

      // Embedded expressions.
      case Literal(EmbeddedExpr(e)) => Constrained.pure({
        e
      }).addConstraint({
        Constraint.equal(e.getType(symbols), expected)
      })

      // Embedded Scala values.
      case Literal(EmbeddedValue(value)) => value match {
        case b : Boolean =>
          Constrained.pure({
            trees.BooleanLiteral(b)
          }).addConstraint({
            Constraint.equal(expected, trees.BooleanType)
          })
        case n : Int => 
          Constrained.pure({
            trees.IntLiteral(n)
          }).addConstraint({
            Constraint.equal(expected, trees.Int32Type)
          })
        case n : BigInt =>
          Constrained.pure({
            trees.IntegerLiteral(n)
          }).addConstraint({
            Constraint.equal(expected, trees.IntegerType)
          })
        case c : Char =>
          Constrained.pure({
            trees.CharLiteral(c)
          }).addConstraint({
            Constraint.equal(expected, trees.CharType)
          })
        case s : String =>
          Constrained.pure({
            trees.StringLiteral(s)
          }).addConstraint({
            Constraint.equal(expected, trees.StringType)
          })
        case _ : Unit =>
          Constrained.pure({
            trees.UnitLiteral()
          }).addConstraint({
            Constraint.equal(expected, trees.UnitType)
          })
        case _ => Constrained.fail("Unsupported embedded value: " + value + ".", expr.pos)
      }

      //---- Operators ----//

      // Unary minus.
      case Operation("-", Seq(arg)) => {
        typeCheck(arg, expected).map(trees.UMinus(_)).addConstraint({
          Constraint.isNumeric(expected)
        })
      }

      // Unary plus.
      case Operation("+", Seq(arg)) => {
        typeCheck(arg, expected).addConstraint({
          Constraint.isNumeric(expected)
        })
      }

      // Binary operation defined on numeric types.
      case Operation(NumericBinOp(op), args) => {

        Constrained.sequence({
          args.map(typeCheck(_, expected))
        }).map({
          case Seq(a, b) => op(a, b)
        }).checkImmediate(
          args.length == 2, "Wrong number of arguments.", expr.pos
        ).addConstraint({
          Constraint.isNumeric(expected)
        })
      }

      // Binary operation defined on integral types.
      case Operation(IntegralBinOp(op), args) => {

        Constrained.sequence({
          args.map(typeCheck(_, expected))
        }).map({
          case Seq(a, b) => op(a, b)
        }).checkImmediate(
          args.length == 2, "Wrong number of arguments.", expr.pos
        ).addConstraint({
          Constraint.isIntegral(expected)
        })
      }

      // Unary negation.
      case Operation("!", Seq(arg)) => {
        typeCheck(arg, expected).map(trees.Not(_)).addConstraint({
          Constraint.equal(expected, trees.BooleanType)
        })
      }

      // Binary operation defined on comparable types.
      case Operation(ComparableBinOp(op), args) => {

        val expectedArg = Unknown.fresh
        
        Constrained.sequence({
          args.map(typeCheck(_, expectedArg))
        }).map({
          case Seq(a, b) => op(a, b)
        }).checkImmediate(
          args.length == 2, "Wrong number of arguments.", expr.pos
        ).addConstraint({
          Constraint.isComparable(expectedArg)
        }).addConstraint({
          Constraint.equal(expected, trees.BooleanType)
        })
      }

      // Binary operation defined on bit vectors.
      case Operation(BitVectorBinOp(op), args) => {
        Constrained.sequence({
          args.map(typeCheck(_, expected))
        }).map({
          case Seq(a, b) => op(a, b)
        }).checkImmediate(
          args.length == 2, "Wrong number of arguments.", expr.pos
        ).addConstraint({
          Constraint.isBitVector(expected)
        })
      }

      // Equality.
      case Operation("==", args) => {
        
        val expectedArg = Unknown.fresh

        Constrained.sequence({
          args.map(typeCheck(_, expectedArg))
        }).map({
          case Seq(a, b) => trees.Equals(a, b)
        }).checkImmediate(
          args.length == 2, "Wrong number of arguments.", expr.pos
        ).addConstraint({
          Constraint.equal(expected, trees.BooleanType)
        })
      }

      // Inequality.
      case Operation("!=", args) => {
        
        val expectedArg = Unknown.fresh

        Constrained.sequence({
          args.map(typeCheck(_, expectedArg))
        }).map({
          case Seq(a, b) => trees.Not(trees.Equals(a, b))
        }).checkImmediate(
          args.length == 2, "Wrong number of arguments.", expr.pos
        ).addConstraint({
          Constraint.equal(expected, trees.BooleanType)
        })
      }

      // Binary operation defined on comparable types.
      case Operation(BooleanBinOp(op), args) => {
        
        Constrained.sequence({
          args.map(typeCheck(_, expected))
        }).map({
          case Seq(a, b) => op(a, b)
        }).checkImmediate(
          args.length == 2, "Wrong number of arguments.", expr.pos
        ).addConstraint({
          Constraint.equal(expected, trees.BooleanType)
        })
      }

      //---- Operations on Strings ----//

      // String concatenation.
      case ConcatenateOperation(str1, str2) => {
        Constrained.sequence({
          Seq(str1, str2).map(typeCheck(_, expected))
        }).map({
          case Seq(s1, s2) => trees.StringConcat(s1, s2)
        }).addConstraint({
          Constraint.equal(expected, trees.StringType)
        })
      }

      // Substring.
      case SubstringOperation(str, start, end) => {
        val indexExpected = Unknown.fresh

        Constrained.sequence(Seq(
          typeCheck(str, expected),
          typeCheck(start, indexExpected),
          typeCheck(end, indexExpected)
        )).map({
          case Seq(s, a, b) => trees.SubString(s, a, b)
        }).addConstraint({
          Constraint.equal(expected, trees.StringType)
        }).addConstraint({
          Constraint.equal(indexExpected, trees.IntegerType)
        })
      }

      // String length.
      case Application(Literal(Name(bi.BuiltIn(bi.StringLength))), Seq(s)) => {
        val stringExpected = Unknown.fresh
        typeCheck(s, stringExpected).map({
          case e => trees.StringLength(e) 
        }).addConstraint({
          Constraint.equal(stringExpected, trees.StringType)
        }).addConstraint({
          Constraint.equal(expected, trees.IntegerType)
        })
      }

      //---- Operations on Bags ----//

      case BagConstruction(bs, otpe) => {
        val elementType = otpe.getOrElse(Unknown.fresh)
        val freshs = Seq.fill(bs.length)(Unknown.fresh)
        val countType = Unknown.fresh

        Constrained.withUnifier({ (unifier: Unifier) =>
          (es: Seq[(trees.Expr, trees.Expr)]) => trees.FiniteBag(es, unifier(elementType))
        }).app({
          Constrained.sequence({
            bs.zip(freshs).map({
              case ((k, v), t) => {
                typeCheck(k, t).combine(typeCheck(v, countType))({
                  (a: trees.Expr, b: trees.Expr) => (a, b)
                }).addConstraint({
                  Constraint.subtype(t, elementType)
                })
              }
            })
          })
        }).addConstraint({
          Constraint.equal(countType, trees.IntegerType)
        }).addConstraint({
          Constraint.equal(expected, trees.BagType(elementType))
        })
      }

      case BagMultiplicityOperation(map, key, otpe) => {
        val elementType = otpe.getOrElse(Unknown.fresh)
        val keyExpected = Unknown.fresh
        val mapExpected = Unknown.fresh

        typeCheck(map, mapExpected).combine(typeCheck(key, keyExpected))({
          case (m, k) => trees.MultiplicityInBag(k, m)
        }).addConstraint({
          Constraint.equal(expected, trees.IntegerType)
        }).addConstraint({
          Constraint.subtype(keyExpected, elementType)
        }).addConstraint({
          Constraint.equal(mapExpected, trees.BagType(elementType))
        })
      }

      case BagBinaryOperation(map1, map2, op, otpe) => {
        val elementType = otpe.getOrElse(Unknown.fresh)
        val mapExpected = Unknown.fresh

        typeCheck(map1, mapExpected).combine(typeCheck(map2, mapExpected))({
          case (m1, m2) => op(m1, m2)
        }).addConstraint({
          Constraint.equal(mapExpected, trees.BagType(elementType))
        })
      }

      // Bag add operation.
      case BagAddOperation(bag, elem, otpe) => {
        val elementExpected = Unknown.fresh
        val elementType = otpe.getOrElse(Unknown.fresh)

        typeCheck(bag, expected).map({ (b: trees.Expr) => 
          (e: trees.Expr) => trees.BagAdd(b, e)
        }).app({
          typeCheck(elem, elementExpected)
        }).addConstraint({
          Constraint.equal(expected, trees.BagType(elementType))
        }).addConstraint({
          Constraint.subtype(elementExpected, elementType)
        })
      }

      //---- Operations on Maps ----//

      case MapConstruction(default, bs, oKeyType, oValueType) => {
        val keyType = oKeyType.getOrElse(Unknown.fresh)
        val valueType = oValueType.getOrElse(Unknown.fresh)
        val defaultFresh = Unknown.fresh
        val freshs = Seq.fill(bs.length)((Unknown.fresh, Unknown.fresh))

        Constrained.withUnifier((unifier: Unifier) => {
          (t: (trees.Expr, Seq[(trees.Expr, trees.Expr)])) => 
            trees.FiniteMap(t._2, t._1, unifier(keyType), unifier(valueType))
        }).app({
          Constrained.sequence({
            bs.zip(freshs).map({
              case ((k, v), (tk, tv)) => {
                typeCheck(k, tk).combine(typeCheck(v, tv))({
                  (a: trees.Expr, b: trees.Expr) => (a, b)
                }).addConstraint({
                  Constraint.subtype(tk, keyType)
                }).addConstraint({
                  Constraint.subtype(tv, valueType)
                })
              }
            })
          }).combine({
            typeCheck(default, defaultFresh).addConstraint({
              Constraint.subtype(defaultFresh, valueType)
            })
          })({
            case (es, e) => (e, es)
          })
        }).addConstraint({
          Constraint.equal(expected, trees.MapType(keyType, valueType))
        })
      }

      case MapApplyOperation(map, key, otpes) => {
        val (keyType, valueType) = otpes.getOrElse((Unknown.fresh, Unknown.fresh))
        val keyExpected = Unknown.fresh
        val mapExpected = Unknown.fresh

        typeCheck(map, mapExpected).combine(typeCheck(key, keyExpected))({
          case (m, k) => trees.MapApply(m, k)
        }).addConstraint({
          Constraint.subtype(keyExpected, keyType)
        }).addConstraint({
          Constraint.equal(expected, valueType)
        }).addConstraint({
          Constraint.equal(mapExpected, trees.MapType(keyType, valueType))
        })
      }

      case MapUpdatedOperation(map, key, value, otpes) => {
        val (keyType, valueType) = otpes.getOrElse((Unknown.fresh, Unknown.fresh))
        val keyExpected = Unknown.fresh
        val valueExpected = Unknown.fresh

        Constrained.sequence(Seq(
          typeCheck(map, expected),
          typeCheck(key, keyExpected),
          typeCheck(value, valueExpected)
        )).map({
          case Seq(m, k, v) => trees.MapUpdated(m, k, v)
        }).addConstraint({
          Constraint.equal(expected, trees.MapType(keyType, valueType))
        }).addConstraint({
          Constraint.subtype(keyExpected, keyType)
        }).addConstraint({
          Constraint.subtype(valueExpected, valueType)
        })
      }

      //---- Operations on Set ----//

      // Call to the Set constructor.
      case SetConstruction(es, otpe) => {
        val upper = otpe.getOrElse(Unknown.fresh)
        val lowers = Seq.fill(es.length) { Unknown.fresh }

        Constrained.withUnifier({ (unifier: Unifier) => 
          (elems: Seq[trees.Expr]) => trees.FiniteSet(elems, unifier(upper))
        }).app({
          Constrained.sequence(es.zip(lowers).map{
            case (e, lower) => typeCheck(e, lower).addConstraint({
              Constraint.subtype(lower, upper)
            })
          })
        }).addConstraint({
          Constraint.equal(expected, trees.SetType(upper))
        })
      }

      // Call to contains.
      case ContainsOperation(set, elem, otpe) => {
        val setType = Unknown.fresh
        val elementExpected = Unknown.fresh
        val elementType = otpe.getOrElse(Unknown.fresh)

        typeCheck(set, setType).map({ (s: trees.Expr) => 
          (e: trees.Expr) => trees.ElementOfSet(e, s)
        }).app({
          typeCheck(elem, elementExpected)
        }).addConstraint({
          Constraint.equal(expected, trees.BooleanType)
        }).addConstraint({
          Constraint.equal(setType, trees.SetType(elementType))
        }).addConstraint({
          Constraint.subtype(elementExpected, elementType)
        })
      }

      // Call to subset.
      case SubsetOperation(set1, set2, otpe) => {
        val setType = Unknown.fresh
        val elementType = otpe.getOrElse(Unknown.fresh)

        typeCheck(set1, setType).map({ (s1: trees.Expr) => 
          (s2: trees.Expr) => trees.SubsetOf(s1, s2)
        }).app({
          typeCheck(set2, setType)
        }).addConstraint({
          Constraint.equal(expected, trees.BooleanType)
        }).addConstraint({
          Constraint.equal(setType, trees.SetType(elementType))
        })
      }

      // Binary operations on set that return sets.
      case SetBinaryOperation(set1, set2, f, otpe) => {
        val elementType = otpe.getOrElse(Unknown.fresh)

        typeCheck(set1, expected).map({ (s1: trees.Expr) => 
          (s2: trees.Expr) => f(s1, s2)
        }).app({
          typeCheck(set2, expected)
        }).addConstraint({
          Constraint.equal(expected, trees.SetType(elementType))
        })
      }

      // Set add operation.
      case SetAddOperation(set, elem, otpe) => {
        val elementExpected = Unknown.fresh
        val elementType = otpe.getOrElse(Unknown.fresh)

        typeCheck(set, expected).map({ (s: trees.Expr) => 
          (e: trees.Expr) => trees.SetAdd(s, e)
        }).app({
          typeCheck(elem, elementExpected)
        }).addConstraint({
          Constraint.equal(expected, trees.SetType(elementType))
        }).addConstraint({
          Constraint.subtype(elementExpected, elementType)
        })
      }

      //---- Conditionals ----//

      // Conditional expression.
      case Operation("IfThenElse", Seq(cond, thenn, elze)) => {
        
        val expectedCond = Unknown.fresh

        Constrained.sequence(Seq(
          typeCheck(cond, expectedCond),
          typeCheck(thenn, expected),
          typeCheck(elze, expected)
        )).map({
          case Seq(condExpr, thennExpr, elzeExpr) => trees.IfExpr(condExpr, thennExpr, elzeExpr)
        }).addConstraint({
          Constraint.equal(expectedCond, trees.BooleanType)
        })
      }

      // Assumptions
      case Operation("Assume", Seq(p, e)) => {
        val booleanExpected = Unknown.fresh
        typeCheck(p, booleanExpected).combine(typeCheck(e, expected))({
          case (pred, body) => trees.Assume(pred, body)
        }).addConstraint({
          Constraint.equal(booleanExpected, trees.BooleanType)
        })
      }

      //---- Functions ----//

      // Function invocation.
      case Application(TypedFunDef(fd, optTpeArgs), args) => {

        val freshs = args.map({ case a => Unknown.fresh(a.pos) })

        val constrainedArgs = Constrained.sequence {
          args.zip(freshs).map({ case (e, t) => typeCheck(e, t) })
        }

        val typeParamToFresh = fd.tparams.map({
          (t: trees.TypeParameterDef) => t.tp -> Unknown.fresh
        })

        val instantiator = new symbols.TypeInstantiator(typeParamToFresh.toMap)

        val paramTypes = fd.params.map({
          (vd: trees.ValDef) => instantiator.transform(vd.tpe)
        })

        val invok = Constrained.withUnifier({ (unifier: Unifier) =>
          (realArgs: Seq[trees.Expr]) => trees.FunctionInvocation(fd.id, typeParamToFresh.map({
            case (_, u) => unifier(u)
          }), realArgs)
        })
        
        val constrained = invok.app({
          constrainedArgs
        }).checkImmediate(
          // Their should be the same number of argument applied than parameters of the function.
          args.length == fd.params.length,
          "Wrong number of arguments. " + fd.id + " takes " + fd.params.length + " arguments, " + args.length + " were given.",
          expr.pos
        ).addConstraints({
          // The types of arguments should be subtype of the type of the parameters.
          freshs.zip(paramTypes).map({ case (a, b) => Constraint.subtype(a, b)(a.pos) })
        }).addConstraint({
          // The return type of the function should be what is expected.
          Constraint.equal(instantiator.transform(fd.returnType), expected)
        })

        optTpeArgs match {
          case None => constrained
          case Some(tpeArgs) => {
            constrained.addConstraints({
              // The annotated types should correspond to the type of the parameters.
              tpeArgs.zip(typeParamToFresh.map(_._2)).map({ case (a, b) => Constraint.equal(a, b) })
            }).checkImmediate(
              // Their should be the same number of type applied than type parameters of the function.
              tpeArgs.length == fd.tparams.length,
              "Wrong number of type arguments. " + fd.id + " takes " + fd.tparams.length + "arguments, " + tpeArgs.length + " were given.",
              expr.pos
            )
          }
        }
      }
      
      // Constructor invocation.
      case Application(TypedConsDef(cons, optTpeArgs), args) => {

        val freshs = args.map({ case a => Unknown.fresh(a.pos) })

        val constrainedArgs = Constrained.sequence {
          args.zip(freshs).map({ case (e, t) => typeCheck(e, t) })
        }

        val typeParamToFresh = cons.tparams.map({
          (t: trees.TypeParameterDef) => t.tp -> Unknown.fresh
        })

        val instantiator = new symbols.TypeInstantiator(typeParamToFresh.toMap)

        val paramTypes = cons.fields.map({
          (vd: trees.ValDef) => instantiator.transform(vd.tpe)
        })

        val invok = Constrained.withUnifier({ (unifier: Unifier) =>
          (realArgs: Seq[trees.Expr]) => trees.ADT(cons.typed(typeParamToFresh.map({
            case (_, u) => unifier(u)
          }))(symbols).toType, realArgs)
        })
        
        val constrained = invok.app({
          constrainedArgs
        }).checkImmediate(
          // Their should be the same number of argument applied than parameters of the constructor.
          args.length == cons.fields.length,
          "Wrong number of arguments. Constructor " + cons.id + " takes " + cons.fields.length + " arguments, " + args.length + " were given.",
          expr.pos
        ).addConstraints({
          // The types of arguments should be subtypes of the parameters.
          freshs.zip(paramTypes).map({ case (a, b) => Constraint.subtype(a, b)(a.pos) })
        }).addConstraint({
          // The return type of the constructor application should be what is expected.
          Constraint.equal(cons.typed(typeParamToFresh.map(_._2))(symbols).toType, expected)
        })

        optTpeArgs match {
          case None => constrained
          case Some(tpeArgs) => {
            constrained.addConstraints({
              // The annotated types should correspond to the type of the parameters.
              tpeArgs.zip(typeParamToFresh.map(_._2)).map({ case (a, b) => Constraint.equal(a, b) })
            }).checkImmediate(
              // Their should be the same number of type applied than type parameters of the function.
              tpeArgs.length == cons.tparams.length,
              "Wrong number of type arguments. Constructor " + cons.id + " takes " + cons.tparams.length + " type arguments, " + tpeArgs.length + " were given.",
              expr.pos
            )
          }
        }
      }

      // Tuple Construction.
      case Operation("Tuple", args) => {
        val argsTypes = Seq.fill(args.size)(Unknown.fresh)

        Constrained.sequence(args.zip(argsTypes).map({
          case (e, t) => typeCheck(e, t)
        })).map({
          case es => trees.Tuple(es)
        }).checkImmediate(
          args.size >= 2,
          "Tuples should be of length greater or equal to 2.",
          expr.pos
        ).addConstraint({
          // This assumes that Tuples are invariant. Is this really the case in Inox ?
          Constraint.equal(expected, trees.TupleType(argsTypes))
        })
      }

      // Function application.
      case Application(callee, args) => {
        val expectedCallee = Unknown.fresh
        val expectedArgs = Seq.fill(args.length)(Unknown.fresh)
        val retType = Unknown.fresh

        Constrained.sequence({
          typeCheck(callee, expectedCallee) +: args.zip(expectedArgs).map({
            case (arg, expectedArg) => typeCheck(arg, expectedArg)
          })
        }).map({
          case exprs => trees.Application(exprs.head, exprs.tail)
        }).addConstraint({
          Constraint.subtype(expectedCallee, trees.FunctionType(expectedArgs, retType))
        }).addConstraint({
          Constraint.equal(retType, expected)
        })
      }

      //---- Bindings ----//

      // Let binding.
      case Let(bs, body) if (!bs.isEmpty) => {

        val (ident, otype, value) = bs.head
        val rest = if (bs.tail.isEmpty) {
          body
        }
        else {
          Let(bs.tail, body)
        }

        val inoxIdent = ident match {
          case IdentifierName(name) => inox.FreshIdentifier(name)
          case IdentifierIdentifier(i) => i
        }

        val identType = Unknown.fresh
        val valueType = Unknown.fresh

        val toLet = Constrained.withUnifier { (unifier: Unifier) =>
          (es: Seq[trees.Expr]) => trees.Let(trees.ValDef(inoxIdent, unifier(identType)), es(0), es(1))
        }

        val args = Constrained.sequence(Seq(
          typeCheck(value, valueType),
          typeCheck(rest, expected)(store + ((ident.getName, (inoxIdent, identType))))
        ))

        val constrained = toLet.app({
          args
        }).addConstraint({
          Constraint.subtype(valueType, identType)
        })

        if (otype.isEmpty) {
          constrained
        }
        else {
          constrained.addConstraint({
            Constraint.equal(identType, otype.get)
          })
        }
      }

      // Lambda abstraction.
      case Abstraction(Lambda, bindings, body) => {
        val expectedBody = Unknown.fresh

        val bs = bindings.map({
          case (IdentifierName(name), _) => (inox.FreshIdentifier(name), Unknown.fresh)
          case (IdentifierIdentifier(i), _) => (i, Unknown.fresh)
        })

        val subTypes = Seq.fill(bindings.size)(Unknown.fresh)
        val superType = Unknown.fresh

        Constrained.withUnifier({ (unifier: Unifier) => 
          val vds = bs.map({ case (i, t) => trees.ValDef(i, unifier(t)) })

          (bodyExpr: trees.Expr) => trees.Lambda(vds, bodyExpr)
        }).app({
          typeCheck(body, expectedBody)(store ++ bindings.map(_._1.getName).zip(bs))
        }).addConstraints({
          // Type of variable should correspond to those annotated.
          bindings.zip(bs).flatMap({
            case ((_, oType), (_, tpe)) => oType.map(Constraint.equal(_, tpe))
          })
        }).addConstraint({
          // The expected type should be a function.
          Constraint.equal(expected, trees.FunctionType(subTypes, superType))
        }).addConstraints({
          // Type of arguments should be super types of expected type arguments.
          bs.map(_._2).zip(subTypes).map({
            case (sup, sub) => Constraint.subtype(sub, sup)
          })
        }).addConstraint({
          // Return type of the function should be a subtype of the expected return type.
          Constraint.subtype(expectedBody, superType)
        })
      }

      // Forall-Quantification.
      case Abstraction(Forall, bindings, body) => {

        val bs = bindings.map({
          case (IdentifierName(name), _) => (inox.FreshIdentifier(name), Unknown.fresh)
          case (IdentifierIdentifier(i), _) => (i, Unknown.fresh)
        })

        Constrained.withUnifier({ (unifier: Unifier) => 
          val vds = bs.map({ case (i, t) => trees.ValDef(i, unifier(t)) })

          (bodyExpr: trees.Expr) => trees.Forall(vds, bodyExpr)
        }).app({
          typeCheck(body, expected)(store ++ bindings.map(_._1.getName).zip(bs))
        }).addConstraints({
          // Type of variable should correspond to those annotated.
          bindings.zip(bs).flatMap({
            case ((_, oType), (_, tpe)) => oType.map(Constraint.equal(_, tpe))
          })
        }).addConstraint({
          // The expected type should be boolean.
          Constraint.equal(expected, trees.BooleanType)
        })
      }

      // Exists-Quantification.
      case Abstraction(Exists, bindings, body) => {

        val bs = bindings.map({
          case (IdentifierName(name), _) => (inox.FreshIdentifier(name), Unknown.fresh)
          case (IdentifierIdentifier(i), _) => (i, Unknown.fresh)
        })

        Constrained.withUnifier({ (unifier: Unifier) => 
          val vds = bs.map({ case (i, t) => trees.ValDef(i, unifier(t)) })

          (bodyExpr: trees.Expr) => trees.Not(trees.Forall(vds, trees.not(bodyExpr)))
        }).app({
          typeCheck(body, expected)(store ++ bindings.map(_._1.getName).zip(bs))
        }).addConstraints({
          // Type of variable should correspond to those annotated.
          bindings.zip(bs).flatMap({
            case ((_, oType), (_, tpe)) => oType.map(Constraint.equal(_, tpe))
          })
        }).addConstraint({
          // The expected type should be boolean.
          Constraint.equal(expected, trees.BooleanType)
        })
      }

      case Abstraction(Choose, Seq((id, otype)), body) => {
        val identType = Unknown.fresh
        val predType = Unknown.fresh
        val inoxIdent = id match {
          case IdentifierIdentifier(i) => i
          case IdentifierName(name) => inox.FreshIdentifier(name)
        }
        
        val constrained = Constrained.withUnifier({ (unifier: Unifier) =>
          (pred: trees.Expr) => trees.Choose(trees.ValDef(inoxIdent, unifier(identType)), pred)
        }).app({
          typeCheck(body, predType)(store + (id.getName -> (inoxIdent, identType)))
        }).addConstraint({
          Constraint.equal(predType, trees.BooleanType)
        }).addConstraint({
          Constraint.subtype(identType, expected)
        })

        otype match {
          case Some(tpe) => constrained.addConstraint({
            Constraint.equal(identType, tpe)
          })
          case _ => constrained
        }
      } 

      //---- Type Casting ----//

      // Annotation.
      case TypeApplication(Operation("TypeAnnotation", Seq(expr)), Seq(tpe)) => {
        val sub = Unknown.fresh

        typeCheck(expr, sub).addConstraint({
          Constraint.equal(expected, tpe)
        }).addConstraint({
          Constraint.subtype(sub, tpe)
        })
      }

      // Casting.
      case TypeApplication(Selection(expr, FieldName("asInstanceOf")), Seq(tpe)) => {
        val sup = Unknown.fresh
        val sub = Unknown.fresh
        typeCheck(expr, sub).map({
          (e: trees.Expr) => trees.AsInstanceOf(e, tpe)
        }).addConstraint({
          // The type of the casted expression is the expected type.
          Constraint.equal(tpe, expected)
        }).addConstraint({
          // There should exist a type which is a (non-strict) super type of the annotated type...
          Constraint.subtype(tpe, sup)
        }).addConstraint({
          // ... and a super type of the type of the expression being cast. 
          Constraint.subtype(sub, sup)
        })
      }

      // Instance checking.
      case TypeApplication(Selection(expr, FieldName("isInstanceOf")), Seq(tpe)) => {
        val sup = Unknown.fresh
        val sub = Unknown.fresh
        typeCheck(expr, sub).map({
          (e: trees.Expr) => trees.IsInstanceOf(e, tpe)
        }).addConstraint({
          // The expected type should be Boolean.
          Constraint.equal(expected, trees.BooleanType)
        }).addConstraint({
          // There should exist a type which is a (non-strict) super type of the annotated type...
          Constraint.subtype(tpe, sup)
        }).addConstraint({
          // ... and a super type of the type of the expression being checked. 
          Constraint.subtype(sub, sup)
        })
      }

      //---- Accessors ----//

      // Tuple Selection.
      case Selection(expr, TupleField(i)) => {
        val tupleType = Unknown.fresh
        val memberType = Unknown.fresh

        typeCheck(expr, tupleType).map({
          case tuple => trees.TupleSelect(tuple, i)
        }).addConstraint({
          Constraint.equal(memberType, expected)
        }).addConstraint({
          Constraint.atIndex(tupleType, memberType, i)
        })
      }

      // Field Selection.
      case Selection(expr, Field((cons, vd))) => {
        val expectedExpr = Unknown.fresh

        val typeParamToFresh = cons.tparams.map({
          (t: trees.TypeParameterDef) => t.tp -> Unknown.fresh
        })

        val instantiator = new symbols.TypeInstantiator(typeParamToFresh.toMap)

        val fieldType = instantiator.transform(vd.tpe)
        val adtType = instantiator.transform(cons.typed(symbols).toType)

        typeCheck(expr, expectedExpr).map({
          (e: trees.Expr) => trees.ADTSelector(e, vd.id)
        }).addConstraint({
          // The field type should be what is expected.
          Constraint.equal(fieldType, expected)
        }).addConstraint({
          // The type of the expression being selected should be exactly
          // that of the ADT constructor.
          Constraint.equal(adtType, expectedExpr)
        })
      }

      //---- Others ----//

      case _ => {
        Constrained.fail("Unknown construct.", expr.pos)
      } 
    }
  }
}