package welder
package parsing

import inox._

import scala.util.parsing.input.Position

trait TypeIR extends IR {

  val trees: inox.ast.Trees
  val symbols: trees.Symbols

  type Identifier = Nothing
  type Type = Nothing
  type Field = Nothing
  type Quantifier = Nothing

  sealed abstract class Value
  case class Name(name: String) extends Value { override def toString = name }
  case class EmbeddedType(tpe: trees.Type) extends Value { override def toString = tpe.toString }
  case class EmbeddedIdentifier(id: inox.Identifier) extends Value { override def toString = id.toString }

  sealed abstract class Operator
  case object Group extends Operator
  case object Tuple extends Operator
  case object Arrow extends Operator

  object BVType {
    def unapply(name: String): Option[trees.Type] = {
      if (name.startsWith("Int")) {
        scala.util.Try(name.drop(3).toInt).toOption.filter(_ > 0).map(trees.BVType(_))
      }
      else {
        None
      }
    }
  }

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

  def toInoxType(expr: Expression): Either[Seq[ErrorLocation], trees.Type] = expr match {

    case Operation(Tuple, irs) if irs.size >= 2 => for {
      tpes <- traverse(irs.map(toInoxType(_))).left.map(_.flatten).right
    } yield trees.TupleType(tpes)

    case Operation(Arrow, Seq(Operation(Group, froms), to)) => for {
      argTpes <- traverse(froms.map(toInoxType(_))).left.map(_.flatten).right
      retTpe  <- toInoxType(to).right
    } yield trees.FunctionType(argTpes, retTpe)

    case Operation(Arrow, Seq(from, to)) => for {
      argTpe <- toInoxType(from).right
      retTpe <- toInoxType(to).right
    } yield trees.FunctionType(Seq(argTpe), retTpe)

    case Application(l@Literal(value), irs) => for {
      cons <- parametric.get(value) match {
        case None => Left(Seq(ErrorLocation("Unknown type constructor: " + value, l.pos))).right
        case Some(p) => Right(p).right
      }
      tpes <- traverse(irs.map(toInoxType(_))).left.map(_.flatten).right
      appl <- cons(tpes) match {
        case None => Left(Seq(ErrorLocation("Incorrect number of arguments for type constructor: " + value, l.pos))).right
        case Some(t) => Right(t).right
      }
    } yield appl

    case Literal(EmbeddedType(t)) => Right(t)

    case Literal(Name(BVType(t))) => Right(t)

    case l@Literal(value) => basic.get(value) match {
      case None => Left(Seq(ErrorLocation("Unknown type: " + value, l.pos)))
      case Some(t) => Right(t)
    }

    case _ => Left(Seq(ErrorLocation("Invalid type.", expr.pos)))
  }
}