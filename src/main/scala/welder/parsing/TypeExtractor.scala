package welder
package parsing

trait TypeExtractors { self: Interpolator =>

  import program.trees

  trait TypeExtractor extends Extractor { self: TypeIR.type =>

    def extract(tpe: trees.Type, template: Expression): Option[Match] = {

      (template, tpe) match {
        case (Hole(i), _) => Some(matching(i, tpe))
        case (_, trees.Untyped) => fail
        case (Literal(Name(BVType(templateSize))), trees.BVType(size)) => if (templateSize == size) success else fail
        case (Literal(name), _) if (basic.get(name) == Some(tpe)) => success
        case (Operation(Tuple, templates), trees.TupleType(tpes)) if (templates.length == tpes.length) =>
          Utils.traverse(tpes.zip(templates).map { case (ty, tt) => extract(ty, tt) }).map(_.fold(empty)(_ ++ _))
        case (Operation(Arrow, Seq(templateFrom, templateTo)), trees.FunctionType(froms, to)) => templateFrom match {
          case Operation(Group, templatesFroms) if (templatesFroms.length == froms.length) => for {
            matchingsFroms <- Utils.traverse(froms.zip(templatesFroms).map { case (ty, tt) => extract(ty, tt) }).map(_.fold(empty)(_ ++ _))
            matchingsTo <- extract(to, templateTo)
          } yield matchingsFroms ++ matchingsTo
          case _ if (froms.length == 1) => for {
            matchingsFrom <- extract(froms.head, templateFrom)
            matchingsTo <- extract(to, templateTo)
          } yield matchingsFrom ++ matchingsTo
          case _ => fail
        }
        case (Application(Literal(Name("Set")), Seq(templateElem)), trees.SetType(elem)) =>
          extract(elem, templateElem)
        case (Application(Literal(Name("Bag")), Seq(templateElem)), trees.BagType(elem)) =>
          extract(elem, templateElem)
        case (Application(Literal(Name("Map")), Seq(templateKey, templateValue)), trees.MapType(key, value)) => for {
          matchingsKey <- extract(key, templateKey)
          matchingsValue <- extract(value, templateValue)
        } yield matchingsKey ++ matchingsValue
        case (Application(Hole(index), templates), trees.ADTType(id, tpes)) => for {
          matchings <- Utils.traverse(tpes.zip(templates).map { case (ty, tt) => extract(ty, tt) }).map(_.fold(empty)(_ ++ _))
        } yield matchings ++ matching(index, id)
        case (Application(Literal(Name(name)), templates), trees.ADTType(id, tpes)) if (id.name == name && templates.length == tpes.length) =>
          Utils.traverse(tpes.zip(templates).map { case (ty, tt) => extract(ty, tt) }).map(_.fold(empty)(_ ++ _))
        case (_, _) => fail
      }
    }
  }
}