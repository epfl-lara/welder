package welder
package parsing

import inox._

trait ExprIR extends IR with Constraints with InoxConstraintSolver {
  
  val trees: inox.ast.Trees
  val symbols: trees.Symbols

  sealed abstract class Identifier {
    def getName: String
  }
  case class IdentifierName(name: String) extends Identifier {
    override def getName = name
  }
  case class IdentifierIdentifier(identifier: inox.Identifier) extends Identifier {
    override def getName = identifier.uniqueName
  }

  type Operator = String
  
  sealed abstract class Field
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

  def toInoxExpr(expr: Expression): Option[trees.Expr] = {
    val topType = Unknown.fresh

    typeCheck(expr, topType)(Map()) match {
      case Unsatifiable => None
      case WithConstraints(elaborator, constraints) => solveConstraints(constraints).map { 
        (unifier: Unifier) => elaborator(unifier)
      }
    }
  }

  def typeCheck(expr: Expression, expected: Unknown)
               (implicit store: Map[String, (inox.Identifier, trees.Type)]): Constrained[trees.Expr] = expr match {

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
    }).checkImmediate({
      store.contains(i.uniqueName)
    }).addConstraint({
      Constraint.subtype(store(i.uniqueName)._2, expected)
    })

    // Variable.
    case Variable(variable) => Constrained.withUnifier({ (unifier: Unifier) =>
      val (i, t) = store(variable.getName)
      trees.Variable(i, unifier(t), Set.empty)
    }).checkImmediate({
      store.contains(variable.getName)
    }).addConstraint({
      Constraint.subtype(store(variable.getName)._2, expected)
    })

    //---- Embedded values ----//

    // Embedded expressions.
    case Literal(EmbeddedExpr(e)) => Constrained.pure({
      e
    }).addConstraint({
      Constraint.subtype(e.getType(symbols), expected)
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
      case _ => Unsatifiable
    }

    //---- Operators ----//

    // Unary minus.
    case Operation("-", Seq(arg)) => {
      typeCheck(arg, expected).map(trees.UMinus(_)).addConstraint({
        Constraint.isNumeric(expected)
      })
    }

    // Binary operation defined on numeric types.
    case Operation(NumericBinOp(op), args) => {

      Constrained.sequence({
        args.map(typeCheck(_, expected))
      }).map({
        case Seq(a, b) => op(a, b)
      }).checkImmediate({
        args.length == 2
      }).addConstraint({
        Constraint.isNumeric(expected)
      })
    }

    // Binary operation defined on integral types.
    case Operation(IntegralBinOp(op), args) => {

      Constrained.sequence({
        args.map(typeCheck(_, expected))
      }).map({
        case Seq(a, b) => op(a, b)
      }).checkImmediate({
        args.length == 2
      }).addConstraint({
        Constraint.isIntegral(expected)
      })
    }

    // Binary operation defined on comparable types.
    case Operation(ComparableBinOp(op), args) => {

      val expectedArg = Unknown.fresh
      
      Constrained.sequence({
        args.map(typeCheck(_, expectedArg))
      }).map({
        case Seq(a, b) => op(a, b)
      }).checkImmediate({
        args.length == 2
      }).addConstraint({
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
      }).checkImmediate({
        args.length == 2
      }).addConstraint({
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
      }).checkImmediate({
        args.length == 2
      }).addConstraint({
        Constraint.equal(expected, trees.BooleanType)
      })
    }

    // Binary operation defined on comparable types.
    case Operation(BooleanBinOp(op), args) => {
      
      Constrained.sequence({
        args.map(typeCheck(_, expected))
      }).map({
        case Seq(a, b) => op(a, b)
      }).checkImmediate({
        args.length == 2
      }).addConstraint({
        Constraint.equal(expected, trees.BooleanType)
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

    //---- Functions ----//

    // Function invocation.
    case Application(TypedFunDef(fd, optTpeArgs), args) => {

      val freshs = Seq.fill(args.length) { Unknown.fresh }

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
      }).checkImmediate({
        // Their should be the same number of argument applied than parameters of the function.
        args.length == fd.params.length
      }).addConstraints({
        // The types of arguments should be of the type of the parameters.
        freshs.zip(paramTypes).map({ case (a, b) => Constraint.equal(a, b) })
      }).addConstraint({
        // The return type of the function should be a subtype of what is expected.
        Constraint.subtype(instantiator.transform(fd.returnType), expected)
      })

      optTpeArgs match {
        case None => constrained
        case Some(tpeArgs) => {
          constrained.addConstraints({
            // The annotated types should correspond to the type of the parameters.
            tpeArgs.zip(typeParamToFresh.map(_._2)).map({ case (a, b) => Constraint.equal(a, b) })
          }).checkImmediate({
            // Their should be the same number of type applied than type parameters of the function.
            tpeArgs.length == fd.tparams.length
          })
        }
      }
    }
    
    // Constructor invocation.
    case Application(TypedConsDef(cons, optTpeArgs), args) => {

      val freshs = Seq.fill(args.length) { Unknown.fresh }

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
      }).checkImmediate({
        // Their should be the same number of argument applied than parameters of the function.
        args.length == cons.fields.length
      }).addConstraints({
        // The types of arguments should be of the type of the parameters.
        freshs.zip(paramTypes).map({ case (a, b) => Constraint.equal(a, b) })
      }).addConstraint({
        // The return type of the constructor application should be a subtype of what is expected.
        Constraint.subtype(cons.typed(typeParamToFresh.map(_._2))(symbols).toType, expected)
      })

      optTpeArgs match {
        case None => constrained
        case Some(tpeArgs) => {
          constrained.addConstraints({
            // The annotated types should correspond to the type of the parameters.
            tpeArgs.zip(typeParamToFresh.map(_._2)).map({ case (a, b) => Constraint.equal(a, b) })
          }).checkImmediate({
            // Their should be the same number of type applied than type parameters of the function.
            tpeArgs.length == cons.tparams.length
          })
        }
      }
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
        Constraint.equal(expectedCallee, trees.FunctionType(expectedArgs, retType))
      }).addConstraint({
        Constraint.subtype(retType, expected)
      })
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

    //---- Type Casting ----//

    // Casting.
    case TypeApplication(Selection(expr, FieldName("asInstanceOf")), Seq(tpe)) => {
      val sup = Unknown.fresh
      val sub = Unknown.fresh
      typeCheck(expr, sub).map({
        (e: trees.Expr) => trees.AsInstanceOf(e, tpe)
      }).addConstraint({
        // The type of the casted expression should be a subtype of the expected type.
        Constraint.subtype(tpe, expected)
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
        Constraint.subtype(expected, trees.BooleanType)
      }).addConstraint({
        // There should exist a type which is a (non-strict) super type of the annotated type...
        Constraint.subtype(tpe, sup)
      }).addConstraint({
        // ... and a super type of the type of the expression being checked. 
        Constraint.subtype(sub, sup)
      })
    }

    //---- Accessors ----//

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
        // The field type should be a subtype of what is expected.
        Constraint.subtype(fieldType, expected)
      }).addConstraint({
        // The type of the expression being selected should be exactly
        // that of the ADT constructor.
        Constraint.equal(adtType, expectedExpr)
      })
    }

    //---- Others ----//

    case _ => {
      Constrained.fail
    } 
  }
}