
package welder
package example

import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

object ListTreeProgram {

  val list: Identifier = FreshIdentifier("List")
  val cons: Identifier = FreshIdentifier("Cons")
  val nil: Identifier = FreshIdentifier("Nil")
  val head: Identifier = FreshIdentifier("head")
  val tail: Identifier = FreshIdentifier("tail")

  val tree: Identifier = FreshIdentifier("Tree")
  val branch: Identifier = FreshIdentifier("Branch")
  val leaf: Identifier = FreshIdentifier("Leaf")
  val left: Identifier = FreshIdentifier("left")
  val right: Identifier = FreshIdentifier("right")
  val value: Identifier = FreshIdentifier("value")

  val concatenate: Identifier = FreshIdentifier("concatenate")
  val toList: Identifier = FreshIdentifier("toList")

  val treeMap: Identifier = FreshIdentifier("treeMap")
  val listMap: Identifier = FreshIdentifier("listMap")

  val listSort = mkSort(list)("A")(Seq(cons, nil))
  val treeSort = mkSort(tree)("A")(Seq(branch, leaf))

  val consConstructor = mkConstructor(cons)("A")(Some(list)) {
    case Seq(tp) =>
      Seq(ValDef(head, tp), ValDef(tail, T(list)(tp)))
  }
  val nilConstructor = mkConstructor(nil)("A")(Some(list))(tps => Seq.empty)
  val branchConstructor = mkConstructor(branch)("A")(Some(tree)) {
    case Seq(tp) =>
      Seq(ValDef(left, T(tree)(tp)), ValDef(right, T(tree)(tp)))
  }
  val leafConstructor = mkConstructor(leaf)("A")(Some(tree)) {
    case Seq(tp) =>
      Seq(ValDef(value, tp))
  }

  val concatenateFunction = mkFunDef(concatenate)("A") { case Seq(tpe) =>
    val args: Seq[ValDef] = Seq("as" :: T(list)(tpe), "bs" :: T(list)(tpe))
    val retType: Type = T(list)(tpe)
    val body: Seq[Variable] => Expr = { case Seq(as, bs) =>
      if_ (as.isInstOf(T(cons)(tpe))) {
        let ("cAs" :: T(cons)(tpe), as.asInstOf(T(cons)(tpe))) { case cAs =>
          T(cons)(tpe)(cAs.getField(head), E(concatenate)(tpe)(cAs.getField(tail), bs))
        }
      } else_ {
        bs
      }
    }

    (args, retType, body)
  }

  val toListFunction = mkFunDef(toList)("A") { case Seq(tpe) =>
    val args: Seq[ValDef] = Seq("t" :: T(tree)(tpe))
    val retType: Type = T(list)(tpe)
    val body: Seq[Variable] => Expr = { case Seq(t) =>
      if_ (t.isInstOf(T(branch)(tpe))) {
        let ("b" :: T(branch)(tpe), t.asInstOf(T(branch)(tpe))) { case b =>
          E(concatenate)(tpe)(
            E(toList)(tpe)(b.getField(left)),
            E(toList)(tpe)(b.getField(right)))
        }
      } else_ {
        T(cons)(tpe)(t.asInstOf(T(leaf)(tpe)).getField(value), T(nil)(tpe)())
      }
    }

    (args, retType, body)
  }

  val treeMapFunction = mkFunDef(treeMap)("A", "B") { case Seq(tpeA, tpeB) =>
    val args: Seq[ValDef] = Seq("t" :: T(tree)(tpeA), "f" :: (tpeA =>: tpeB))
    val retType: Type = T(tree)(tpeB)
    val body: Seq[Variable] => Expr = { case Seq(t, f) =>
      if_ (t.isInstOf(T(branch)(tpeA))) {
        let ("b" :: T(branch)(tpeA), t.asInstOf(T(branch)(tpeA))) { case b =>
          T(branch)(tpeB)(
            E(treeMap)(tpeA, tpeB)(b.getField(left), f),
            E(treeMap)(tpeA, tpeB)(b.getField(right), f))
        }
      } else_ {
        T(leaf)(tpeB)(f(t.asInstOf(T(leaf)(tpeA)).getField(value)))
      }
    }

    (args, retType, body)
  }

  val listMapFunction = mkFunDef(listMap)("A", "B") { case Seq(tpeA, tpeB) =>
    val args: Seq[ValDef] = Seq("t" :: T(list)(tpeA), "f" :: (tpeA =>: tpeB))
    val retType: Type = T(list)(tpeB)
    val body: Seq[Variable] => Expr = { case Seq(xs, f) =>
      if_ (xs.isInstOf(T(cons)(tpeA))) {
        let ("cXs" :: T(cons)(tpeA), xs.asInstOf(T(cons)(tpeA))) { case cXs =>
          T(cons)(tpeB)(
            f(cXs.getField(head)),
            E(listMap)(tpeA, tpeB)(cXs.getField(tail), f))
        }
      } else_ {
        T(nil)(tpeB)()
      }
    }

    (args, retType, body)
  }

  val program = InoxProgram(Context.empty, NoSymbols
    .withFunctions(Seq(concatenateFunction, toListFunction, listMapFunction, treeMapFunction))
    .withADTs(Seq(listSort, consConstructor, nilConstructor, treeSort, branchConstructor, leafConstructor)))
  val theory = theoryOf(program)
  import theory._

  val tA = IntegerType
  val tB = IntegerType

  def mapCommutes(t: Expr) = forall("f" :: (tA =>: tB)) { case (f) => 
    E(toList)(tB)(E(treeMap)(tA, tB)(t, f)) === E(listMap)(tA, tB)(E(toList)(tA)(t), f) 
  }

  lazy val mapCommutesThm = structuralInduction(mapCommutes _, T(tree)(tA)) { case (ihs, goal) =>
    ihs.expression match {
      case C(`branch`, left, right) => {

        goal.by(andI(ihs.hypothesis(left), ihs.hypothesis(right)))
      }
      case C(`leaf`, value) => goal.trivial
    }
  }
}
