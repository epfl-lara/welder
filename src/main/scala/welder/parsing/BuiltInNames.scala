
package welder
package parsing

trait BuiltInNames {

  sealed abstract class BuiltIn

  case object AsInstanceOf extends BuiltIn
  case object IsInstanceOf extends BuiltIn

  case object StringConcatenate extends BuiltIn
  case object StringLength extends BuiltIn
  case object StringSubstring extends BuiltIn

  case object SetConstructor extends BuiltIn
  case object SetContains extends BuiltIn
  case object SetAdd extends BuiltIn
  case object SetUnion extends BuiltIn
  case object SetIntersection extends BuiltIn
  case object SetDifference extends BuiltIn
  case object SetSubset extends BuiltIn

  case object BagConstructor extends BuiltIn
  case object BagMultiplicity extends BuiltIn
  case object BagAdd extends BuiltIn
  case object BagUnion extends BuiltIn
  case object BagIntersection extends BuiltIn
  case object BagDifference extends BuiltIn

  case object MapConstructor extends BuiltIn
  case object MapApply extends BuiltIn
  case object MapUpdated extends BuiltIn

  val names: Map[String, BuiltIn]

  object BuiltIn {
    def unapply(name: String): Option[BuiltIn] = {
      names.get(name)
    }
  }
}

trait DefaultBuiltIns extends BuiltInNames {
  override val names: Map[String, BuiltIn] = Map(
    AsInstanceOf -> "asInstanceOf",
    IsInstanceOf -> "isInstanceOf",

    StringConcatenate -> "concatenate",
    StringLength -> "length",
    StringSubstring -> "substring",

    SetConstructor -> "Set",
    SetContains -> "contains",
    SetAdd -> "add",
    SetUnion -> "union",
    SetIntersection -> "intersection",
    SetDifference -> "difference",
    SetSubset -> "subset",

    BagConstructor -> "Bag",
    BagMultiplicity -> "multiplicity",
    BagAdd -> "bagAdd",
    BagUnion -> "bagUnion",
    BagIntersection -> "bagIntersection",
    BagDifference -> "bagDifference",

    MapConstructor -> "Map",
    MapApply -> "apply",
    MapUpdated -> "updated").map(_.swap)
}

trait EmptyBuiltIns extends BuiltInNames {

  override val names: Map[String, BuiltIn] = Map()
}