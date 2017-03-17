package welder
package parsing

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._

trait InoxConstraintSolver { self : Constraints =>

  val typeId = FreshIdentifier("Type")
  val typeType = ADTType(typeId, Seq())
  val nameId = FreshIdentifier("Name")
  val nameType = ADTType(nameId, Seq())
  val isSubtypeId = FreshIdentifier("isSubtype")
  val isBitVectorId = FreshIdentifier("isBitVector")
  val isIntegralId = FreshIdentifier("isIntegral")
  val isNumericId = FreshIdentifier("isNumeric")

  sealed abstract class TypeCons(val name: String, val params: Int)
  case object Set_ extends TypeCons("Set", 1)
  case object Map_ extends TypeCons("Map", 2)
  case object Bag extends TypeCons("Bag", 1)
  case class Fun(n: Int) extends TypeCons("Fun" + n, n + 1)
  case class Tup(n: Int) extends TypeCons("Tuple" + n, n)
  case class ADT_(n: Int) extends TypeCons("ADT" + n, n)
  case class Prim(tpe: trees.Type) extends TypeCons(tpe.toString, 0)

  def getTypeCons(tpe: trees.Type): TypeCons = tpe match {
    case trees.ADTType(i, ts) => ADT_(ts.length)
    case trees.TupleType(ts) => Tup(ts.length)
    case trees.SetType(_) => Set_
    case trees.MapType(_, _) => Map_
    case trees.BagType(_) => Bag
    case trees.FunctionType(froms, _) => Fun(froms.length)
    case _ => Prim(tpe)
  }

  def solveConstraints(constraints: Seq[Constraint]): Option[Unifier] = {

    var constructors: Map[TypeCons, ADTConstructor] = Map()
    var names: Map[Identifier, ADTConstructor] = Map()
    var adtFields: Map[Int, Seq[Identifier]] = Map()
    var tupleFields: Map[Int, Seq[Identifier]] = Map()
    var variables: Map[Unknown, Variable] = Map()
    var atIndexIsIds: Map[Int, Identifier] = Map()

    def registerName(i: Identifier) {
      val consName = FreshIdentifier("Name_" + i)
      val constructor = mkConstructor(consName)()(Some(nameId)) {
        case Seq() => Seq()
      }

      names += (i -> constructor)
    }

    def ensureNameExists(i: Identifier) {
      if (!names.contains(i)) {
        registerName(i)
      }
    }

    def registerConstructor(tc: TypeCons) {
      val consName = FreshIdentifier(tc.name)

      val constructor = mkConstructor(consName)()(Some(typeId)) {
        case Seq() => {
          val ps = 1.to(tc.params).map {
            case i => ("t" + i) :: typeType
          }

          tc match {
            case ADT_(n) => {
              val fs = ("name" :: nameType) +: ps
              adtFields += (n -> fs.map(_.id))
              fs
            }
            case Tup(n) => {
              tupleFields += (n -> ps.map(_.id))
              ps
            }
            case _ => ps
          }
        }
      }

      constructors += (tc -> constructor)
    }

    def ensureConstructorsExists(tpe: trees.Type) {
      if (tpe.isInstanceOf[Unknown]) {
        return;
      }

      tpe match {
        case t@trees.ADTType(i, _) => {
          val adtDef = t.getADT(symbols)
          val root = adtDef.root
          if (adtDef != root) {
            ensureConstructorsExists(root.toType)
          }
          ensureNameExists(i)
        }
        case _ => ()
      }

      val tc = getTypeCons(tpe)

      if (!constructors.contains(tc)) {
        registerConstructor(tc)
      }

      val trees.NAryType(inners, _) = tpe

      for (inner <- inners) ensureConstructorsExists(inner)
    }

    def ensureConstructorsExistForConstraint(c: Constraint) {
      for (tpe <- c.types) {
        ensureConstructorsExists(tpe)
      }

      c match {
        case IsComparable(a) => {
          ensureConstructorsExists(trees.CharType)
        }
        case _ => ()
      }
    }

    def ensureFunctionsIdentifiersExistForConstraint(c: Constraint) {
      c match {
        case AtIndexEqual(_, _, i) => {
          val name = "at" + i + "is"
          val id = FreshIdentifier(name)
          atIndexIsIds += (i -> id)
        }
        case _ => ()
      }
    }

    def toVariable(u: Unknown): Expr = variables.get(u) match {
      case Some(v) => v
      case None => {
        val v = Variable.fresh("m" + u.param, ADTType(typeId, Seq()))
        variables += (u -> v)
        v
      }
    }

    def typeToExpr(tpe: trees.Type): Expr = tpe match {
      case u: Unknown => toVariable(u)
      case trees.ADTType(i, ts) => {
        val tc = getTypeCons(tpe)
        ADT(ADTType(constructors(tc).id, Seq()), ADT(ADTType(names(i).id, Seq()), Seq()) +: ts.map(typeToExpr(_)))
      }
      case trees.NAryType(ts, _) => {
        val tc = getTypeCons(tpe)
        ADT(ADTType(constructors(tc).id, Seq()), ts.map(typeToExpr(_)))
      }
    }

    def constraintToExpr(constraint: Constraint): Expr = constraint match {
      case Equal(a, b) => Equals(typeToExpr(a), typeToExpr(b))
      case Subtype(a, b) => FunctionInvocation(isSubtypeId, Seq(), Seq(typeToExpr(a), typeToExpr(b)))
      case IsNumeric(a) => FunctionInvocation(isNumericId, Seq(), Seq(typeToExpr(a)))
      case IsIntegral(a) => FunctionInvocation(isIntegralId, Seq(), Seq(typeToExpr(a)))
      case IsBitVector(a) => FunctionInvocation(isBitVectorId, Seq(), Seq(typeToExpr(a)))
      case IsComparable(a) => {
        val exprA = typeToExpr(a)
        Or(Equals(exprA, typeToExpr(trees.CharType)), 
           FunctionInvocation(isNumericId, Seq(), Seq(exprA)))
      }
      case AtIndexEqual(a, b, i) => FunctionInvocation(atIndexIsIds(i), Seq(), Seq(typeToExpr(a), typeToExpr(b)))
    }

    for (constraint <- constraints) {
      ensureConstructorsExistForConstraint(constraint)
      ensureFunctionsIdentifiersExistForConstraint(constraint)
    }

    val bvTypes: Seq[Expr] = {
      constructors.keys.collect {
        case Prim(t@trees.BVType(_)) => typeToExpr(t)
      }.toSeq
    }

    val isBitVectorFd = mkFunDef(isBitVectorId)() { case Seq() => (
      Seq("t" :: typeType),
      BooleanType,
      { case Seq(t) =>
        or(bvTypes.map(Equals(t, _)) : _*)
      }
    )}

    val integralTypes: Seq[Expr] = {
      val ts = constructors.keys.collect {
        case Prim(t@trees.IntegerType) => typeToExpr(t)
        case Prim(t@trees.BVType(_)) => typeToExpr(t)
      }
      if (!ts.isEmpty) {
        ts.toSeq
      } else {
        val defaultIntegral = trees.IntegerType

        ensureConstructorsExists(defaultIntegral)

        Seq(typeToExpr(defaultIntegral))
      }
    }

    val isIntegralFd = mkFunDef(isIntegralId)() { case Seq() => (
      Seq("t" :: typeType),
      BooleanType,
      { case Seq(t) =>
        or(integralTypes.map(Equals(t, _)) : _*)
      }
    )}

    val numericTypes: Seq[Expr] = {
      val ts = constructors.keys.collect {
        case Prim(t@trees.RealType) => typeToExpr(t)
      }
      
      ts.toSeq ++ integralTypes
    }

    val isNumericFd = mkFunDef(isNumericId)() { case Seq() => (
      Seq("t" :: typeType),
      BooleanType,
      { case Seq(t) =>
        or(numericTypes.map(Equals(t, _)) : _*)
      }
    )}

    val subtypesPairs = names.keys.toSeq.flatMap({ (i: Identifier) =>
      val sub = symbols.getADT(i)
      val sup = sub.root(symbols)

      if (sub != sup && names.contains(sup.id)) {
        Seq((sub.tparams.length, sub.id, sup.id))
      }
      else {
        Seq()
      }
    }).groupBy(_._1)

    val isSubtypeFd = mkFunDef(isSubtypeId)() { case Seq() => (
      Seq("sub" :: typeType, "sup" :: typeType),
      BooleanType,
      { case Seq(sub, sup) =>

        val cases = (for ((arity, pairs) <- subtypesPairs) yield {

          val adtType = ADTType(constructors(ADT_(arity)).id, Seq())

          if_(and(IsInstanceOf(sub, adtType), IsInstanceOf(sup, adtType))) {
            val subADT = AsInstanceOf(sub, adtType)
            val supADT = AsInstanceOf(sup, adtType)

            val nameSubtype = or((for ((_, a, b) <- pairs) yield {
              and(Equals(ADTSelector(subADT, adtFields(arity)(0)), ADT(ADTType(names(a).id, Seq()), Seq())), 
                  Equals(ADTSelector(supADT, adtFields(arity)(0)), ADT(ADTType(names(b).id, Seq()), Seq())))
            }) : _*)

            val typeArgsEqual = for (field <- adtFields(arity).tail) yield {
              Equals(ADTSelector(subADT, field), ADTSelector(supADT, field))
            }

            And(nameSubtype +: typeArgsEqual)
          } else_ {
            BooleanLiteral(false)
          }

        }).toSeq

        or((Equals(sub, sup) +: cases) : _*)
      }
    )}

    val atIndexIsFds = {

      atIndexIsIds.toSeq.map({ case (i, id) => 
        mkFunDef(id)() { case Seq() => (
          Seq("tup" :: typeType, "mem" :: typeType),
          BooleanType,
          { case Seq(tup, mem) =>
            val zero: Expr = BooleanLiteral(false)
            constructors.keys.collect({
              case Tup(k) if k >= i => k
            }).foldLeft(zero) { (rest: Expr, k: Int) =>
              val tupleType = ADTType(constructors(Tup(k)).id, Seq())

              if_(IsInstanceOf(tup, tupleType)) {
                val asTuple = AsInstanceOf(tup, tupleType)
                Equals(ADTSelector(asTuple, tupleFields(k)(i - 1)), mem)
              } else_ { 
                rest
              }
            }
          }
        )}
      })
    }

    val allNames = names.values.toSeq
    val nameSort = mkSort(nameId)()(allNames.map(_.id))
    val allConstructors = constructors.values.toSeq
    val typeSort = mkSort(typeId)()(allConstructors.map(_.id))

    val adts =
      if (allNames.isEmpty) typeSort +: allConstructors
      else Seq(nameSort, typeSort) ++ allConstructors ++ allNames

    val progSymbols = NoSymbols
                    .withADTs(adts)
                    .withFunctions(Seq(isSubtypeFd, isNumericFd, isIntegralFd, isBitVectorFd) ++ atIndexIsFds)

    val program = InoxProgram(Context.empty, progSymbols)
    val solver = program.getSolver.getNewSolver

    try {
      for (constraint <- constraints) {
        val e = constraintToExpr(constraint)
        solver.assertCnstr(e)
      }

      solver.check(SolverResponses.Model) match {
        case SolverResponses.SatWithModel(model) => {

          val unknownTable = variables.map(_.swap)
          val tcTable = constructors.map { case (tc, adtcons) => (adtcons.id -> tc) }
          val adtTable = names.map { case (i, adtcons) => (adtcons.id -> i) }

          def exprToADT(expr: Expr): Identifier = expr match {
            case ADT(tpe, Seq()) => adtTable(tpe.id)
          }

          def exprToType(expr: Expr): trees.Type = expr match {
            case Variable(_, _, _) => throw new Error("Uninstantiated meta variable in the model.")
            case ADT(tpe, args) => {

              (args, tcTable(tpe.id)) match {
                case (Seq(t), Set_)     => trees.SetType(exprToType(t))
                case (Seq(f, t), Map_)  => trees.MapType(exprToType(f), exprToType(t))
                case (Seq(t), Bag)      => trees.BagType(exprToType(t))
                case (ts, Fun(_))       => trees.FunctionType(ts.tail.map(exprToType(_)), exprToType(ts.head))
                case (_, Tup(_))        => trees.TupleType(args.map(exprToType(_)))
                case (_, ADT_(_))       => trees.ADTType(exprToADT(args.head), args.tail.map(exprToType(_)))
                case (Seq(), Prim(tpe)) => tpe
              }
            }
          }

          Some(new Unifier(model.vars.map { case (vd, expr) =>
            unknownTable(vd.toVariable) -> exprToType(expr)
          }))
        }
        case _ => None
      }
    }
    finally {
      solver.free()
    }
  }
}