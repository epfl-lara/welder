package welder
package parsing

import inox._

/** IR for expressions. */
class ExprIR(val program: InoxProgram) extends IR {

  import program.trees
  import program.symbols

  val solver = new SimpleConstraintSolver(program)
  import solver.constraints._

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

  object SetBinaryOperation {
    def unapply(expr: Expression): Option[(Expression, Expression, (trees.Expr, trees.Expr) => trees.Expr)] = expr match {
      case Application(Selection(set1, FieldName(SetBinMethod(f))), Seq(set2)) => Some((set1, set2, f))
      case Operation(SetBinOp(f), Seq(set1, set2)) => Some((set1, set2, f))
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

    object SetBinMethod {
      def unapply(string: String): Option[(trees.Expr, trees.Expr) => trees.Expr] = string match {
        case "union" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetUnion(lhs, rhs) })
        case "intersection" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetIntersection(lhs, rhs) })
        case "difference" => Some({ (lhs: trees.Expr, rhs: trees.Expr) => trees.SetDifference(lhs, rhs) })
        case _ => None
      }
    }
  }

  object SubsetOperation {
    def unapply(expr: Expression): Option[(Expression, Expression)] = expr match {
      case Application(Selection(set1, FieldName("subsetOf")), Seq(set2)) => Some((set1, set2))
      case Operation("⊆", Seq(set1, set2)) => Some((set1, set2))
      case _ => None
    }
  }

  object ContainsOperation {
    def unapply(expr: Expression): Option[(Expression, Expression)] = expr match {
      case Application(Selection(set, FieldName("contains")), Seq(elem)) => Some((set, elem))
      case Operation("∈", Seq(elem, set)) => Some((set, elem))
      case _ => None
    }
  }

  /** Conversion to Inox expression. */
  def toInoxExpr(expr: Expression): trees.Expr = {
    typeCheck(expr, Unknown.fresh)(Map()) match {
      case Unsatifiable => throw new Exception("Unsatifiable.")
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
      Constraint.equal(store(i.uniqueName)._2, expected)
    })

    // Variable.
    case Variable(variable) => Constrained.withUnifier({ (unifier: Unifier) =>
      val (i, t) = store(variable.getName)
      trees.Variable(i, unifier(t), Set.empty)
    }).checkImmediate({
      store.contains(variable.getName)
    }).addConstraint({
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
      case _ => Unsatifiable
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

    // Inequality.
    case Operation("!=", args) => {
      
      val expectedArg = Unknown.fresh

      Constrained.sequence({
        args.map(typeCheck(_, expectedArg))
      }).map({
        case Seq(a, b) => trees.Not(trees.Equals(a, b))
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

    //---- Operations on Set ----//

    // Call to the Set constructor.
    case Application(Variable(IdentifierName("Set")), es) => {
      val upper = Unknown.fresh
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
    case ContainsOperation(set, elem) => {
      val setType = Unknown.fresh
      val elementType = Unknown.fresh

      typeCheck(set, setType).map({ (s: trees.Expr) => 
        (e: trees.Expr) => trees.ElementOfSet(e, s)
      }).app({
        typeCheck(elem, elementType)
      }).addConstraint({
        Constraint.equal(expected, trees.BooleanType)
      }).addConstraint({
        Constraint.equal(setType, trees.SetType(elementType))
      })
    }

    // Call to subset.
    case SubsetOperation(set1, set2) => {
      val setType = Unknown.fresh
      val elementType = Unknown.fresh

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
    case SetBinaryOperation(set1, set2, f) => {
      val elementType = Unknown.fresh

      typeCheck(set1, expected).map({ (s1: trees.Expr) => 
        (s2: trees.Expr) => f(s1, s2)
      }).app({
        typeCheck(set2, expected)
      }).addConstraint({
        Constraint.equal(expected, trees.SetType(elementType))
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
        // The types of arguments should be subtype of the type of the parameters.
        freshs.zip(paramTypes).map({ case (a, b) => Constraint.subtype(a, b) })
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
        // The types of arguments should be subtypes of the parameters.
        freshs.zip(paramTypes).map({ case (a, b) => Constraint.subtype(a, b) })
      }).addConstraint({
        // The return type of the constructor application should be  what is expected.
        Constraint.equal(cons.typed(typeParamToFresh.map(_._2))(symbols).toType, expected)
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

    // Tuple Construction.
    case Operation("Tuple", args) => {
      val argsTypes = Seq.fill(args.size)(Unknown.fresh)

      Constrained.sequence(args.zip(argsTypes).map({
        case (e, t) => typeCheck(e, t)
      })).map({
        case es => trees.Tuple(es)
      }).checkImmediate({
        args.size >= 2
      }).addConstraint({
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

    // Type Annotation.
    case TypeApplication(Selection(expr, FieldName("as")), Seq(tpe)) => {
      val sub = Unknown.fresh
      typeCheck(expr, sub).addConstraint({
        Constraint.equal(tpe, expected)
      }).addConstraint({
        Constraint.subtype(sub, expected)
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
      Constrained.fail
    } 
  }
}