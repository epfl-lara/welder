
package welder

import inox._
import inox.trees._
import inox.trees.dsl._

import org.scalatest._

class MarkingsSuite extends FunSuite {

  object ListTheory extends Theory {

    val list: Identifier = FreshIdentifier("List")
    val cons: Identifier = FreshIdentifier("Cons")
    val nil: Identifier = FreshIdentifier("Nil")
    val head: Identifier = FreshIdentifier("head")
    val tail: Identifier = FreshIdentifier("tail")

    val listSort = mkSort(list)("A")(Seq(cons, nil))
    val consConstructor = mkConstructor(cons)("A")(Some(list)) {
      case Seq(tp) =>
        Seq(ValDef(head, tp), ValDef(tail, T(list)(tp)))
    }
    val nilConstructor = mkConstructor(nil)("A")(Some(list))(tps => Seq.empty)

    override val program = InoxProgram(Context.empty, NoSymbols.withADTs(Seq(listSort, consConstructor, nilConstructor)))
  }

  import ListTheory._

  test("Markings Freshness") {
    var markings: Set[Mark] = Set()
    for (i <- 1 to 100) {
      markings += Mark.fresh
    }

    assert(markings.size == 100)
  }

  test("Markings use: implI") {

    var illegal: Theorem = null

    val legal = implI(BooleanLiteral(false)) { (thm: Theorem) =>

      illegal = thm

      thm
    }

    assert(!illegal.isGloballyValid)
    assert(legal.isGloballyValid)
  }

  test("Markings use: naturalInduction") {

    var illegal1: Theorem = null
    var illegal2: Theorem = null
    var illegal3: Theorem = null

    def property(x: Expr) = GreaterEquals(x, IntegerLiteral(0))

    val legal = naturalInduction(property, IntegerLiteral(0), _.trivial) { case (ihs, goal) =>

      // Save the induction hypotheses.
      illegal1 = ihs.variableGreaterThanBase
      illegal2 = ihs.propertyForVar
      illegal3 = ihs.propertyForLessOrEqualToVar

      goal.by(andI(illegal1, illegal2, illegal3))
    }

    assert(!illegal1.isGloballyValid)
    assert(!illegal2.isGloballyValid)
    assert(!illegal3.isGloballyValid)
    assert(legal.isGloballyValid)
  }

  test("Markings use: structuralInduction") {

    var illegal: Theorem = null

    def property(x: Expr) = Equals(x, x)

    val legal = structuralInduction(property, ADTType(list, Seq(IntegerType))) { case (ihs, goal) =>
      ihs.expression match {
        case Constructor(name, head, tail) if name == cons => {

          // Save the induction hypothesis.
          illegal = ihs.hypothesis(tail).get

          goal.trivial
        }
        case Constructor(name) if name == nil => {
          goal.trivial
        }
      }
    }

    assert(!illegal.isGloballyValid)
    assert(legal.isGloballyValid)
  }
}