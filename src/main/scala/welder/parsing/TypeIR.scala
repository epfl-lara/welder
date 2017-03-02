package welder
package parsing

import inox._

trait TypeIR extends IR {

  val trees: inox.ast.Trees
  val symbols: trees.Symbols

  type Identifier = Nothing
  type Type = Nothing
  type Field = Nothing
  type Quantifier = Nothing

  sealed abstract class Value
  case class Name(name: String) extends Value
  case class EmbeddedType(tpe: trees.Type) extends Value
  case class EmbeddedIdentifier(id: inox.Identifier) extends Value

  sealed abstract class Operator
  case object Group extends Operator
  case object Tuple extends Operator
  case object Arrow extends Operator

  lazy val basic: Map[Value, trees.Type] = Seq(
    "Boolean" -> trees.BooleanType,
    "BigInt"  -> trees.IntegerType,
    "Char"    -> trees.CharType,
    "Int"     -> trees.Int32Type,
    "Real"    -> trees.RealType,
    "String"  -> trees.StringType,
    "Unit"    -> trees.UnitType).map({ case (n, v) => Name(n) -> v }).toMap

  lazy val parametric: Map[Value, Seq[trees.Type] => Option[trees.Type]] =
    (primitives ++ adts).toMap

  lazy val primitives = Seq(
    "Set" -> withNParams(1, (ts: Seq[trees.Type]) => trees.SetType(ts.head)),
    "Map" -> withNParams(2, (ts: Seq[trees.Type]) => trees.MapType(ts(0), ts(1))),
    "Bag" -> withNParams(1, (ts: Seq[trees.Type]) => trees.BagType(ts.head))).map({ case (n, v) => Name(n) -> v })

  lazy val adts = symbols.adts.toSeq.flatMap({
    case (i, d) => {
      val f = withNParams(d.tparams.length, (ts: Seq[trees.Type]) => trees.ADTType(i, ts))

      Seq(
        Name(i.name) -> f,
        EmbeddedIdentifier(i) -> f)
    }
  })

  def withNParams(n: Int, f: Seq[trees.Type] => trees.Type): Seq[trees.Type] => Option[trees.Type] = {
    case xs if xs.length == n => Some(f(xs))
    case _ => None
  }

  import Utils.traverse

  def toInoxType(expr: Expression): Option[trees.Type] = expr match {

    case Operation(Tuple, irs) if irs.size >= 2 => for {
      tpes <- traverse(irs.map(toInoxType(_)))
    } yield trees.TupleType(tpes)

    case Operation(Arrow, Seq(Operation(Group, froms), to)) => for {
      argTpes <- traverse(froms.map(toInoxType(_)))
      retTpe  <- toInoxType(to)
    } yield trees.FunctionType(argTpes, retTpe)

    case Operation(Arrow, Seq(from, to)) => for {
      argTpe <- toInoxType(from)
      retTpe <- toInoxType(to)
    } yield trees.FunctionType(Seq(argTpe), retTpe)

    case Application(Literal(value), irs) => for {
      cons <- parametric.get(value)
      tpes <- traverse(irs.map(toInoxType(_)))
      appl <- cons(tpes)
    } yield appl

    case Literal(EmbeddedType(t)) => Some(t)

    case Literal(value) => basic.get(value)

    case _ => None
  }
}