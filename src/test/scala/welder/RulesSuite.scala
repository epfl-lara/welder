/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.trees._
import inox.trees.dsl._

import org.scalatest._

class RulesSuite extends FunSuite {

  val sup = FreshIdentifier("Sup")
  val subA = FreshIdentifier("SubA")
  val subB = FreshIdentifier("SubB")

  val supSort = mkSort(sup)()(Seq(subA, subB))
  val subACons = mkConstructor(subA)()(Some(sup)) {
    case Seq() => Seq()
  }
  val subBCons = mkConstructor(subB)()(Some(sup)) {
    case Seq() => Seq()
  }

  val program = InoxProgram(Context.empty, NoSymbols.withADTs(Seq(supSort, subACons, subBCons)))
  val theory = theoryOf(program)

  import theory._

  def assertSuccessful(attempt: => Attempt[_]) {
    assert(attempt.isSuccessful)
  }

  def assertFailure(attempt: => Attempt[_]) {
    assert(!attempt.isSuccessful)
  }

  test("forallE accepts subtypes") {
    val quantified = forallI("sup" :: T(sup)()) { case _ => truth }

    val x = Variable.fresh("x", T(sup)())
    assertSuccessful(forallE(quantified)(x))

    val y = Variable.fresh("y", T(subA)())
    assertSuccessful(forallE(quantified)(y))

    val z = Variable.fresh("z", T(subB)())
    assertSuccessful(forallE(quantified)(z))
  }

  test("forallE does NOT accept super types") {
    val quantified = forallI("sub" :: T(subA)()) { case _ => truth }

    val x = Variable.fresh("x", T(sup)())
    assertFailure(forallE(quantified)(x))
  }

  test("forallE does NOT accept unrelated types") {
    val quantified = forallI("sub" :: T(subA)()) { case _ => truth }

    val x = Variable.fresh("x", T(subB)())
    assertFailure(forallE(quantified)(x))

    val y = Variable.fresh("y", IntegerType)
    assertFailure(forallE(quantified)(y))

    val z = Variable.fresh("z", StringType)
    assertFailure(forallE(quantified)(z))
  }

  test("forallE also works correctly for flat types") {
    val quantified = forallI("n" :: BooleanType) { case _ => truth }

    val x = Variable.fresh("x", BooleanType)
    assertSuccessful(forallE(quantified)(x))

    val y = Variable.fresh("y", IntegerType)
    assertFailure(forallE(quantified)(y))

    val z = Variable.fresh("z", StringType)
    assertFailure(forallE(quantified)(z))

    val r = Variable.fresh("r", T(sup)())
    assertFailure(forallE(quantified)(r))

    val s = Variable.fresh("s", T(subA)())
    assertFailure(forallE(quantified)(s))

    val t = Variable.fresh("t", T(subB)())
    assertFailure(forallE(quantified)(t))
  }
}