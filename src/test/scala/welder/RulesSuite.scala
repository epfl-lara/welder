/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.trees._
import inox.trees.interpolator._

import org.scalatest._

class RulesSuite extends FunSuite {

  val program = Program(inox.trees)(NoSymbols.withSorts(Seq(td"type Sup = SubA() | SubB()")))
  val theory = theoryOf(program)

  import theory._

  def assertSuccessful(attempt: => Attempt[_]) {
    assert(attempt.isSuccessful)
  }

  def assertFailure(attempt: => Attempt[_]) {
    assert(!attempt.isSuccessful)
  }

  test("forallE does NOT accept unrelated types") {
    val quantified = forallI(vd"x: Sup") { case _ => truth }

    val y = Variable.fresh("y", IntegerType())
    assertFailure(forallE(quantified)(y))

    val z = Variable.fresh("z", StringType())
    assertFailure(forallE(quantified)(z))
  }

  test("forallE also works correctly for flat types") {
    val quantified = forallI(vd"n: Boolean") { case _ => truth }

    val x = Variable.fresh("x", BooleanType())
    assertSuccessful(forallE(quantified)(x))

    val y = Variable.fresh("y", IntegerType())
    assertFailure(forallE(quantified)(y))

    val z = Variable.fresh("z", StringType())
    assertFailure(forallE(quantified)(z))

    val r = Variable.fresh("r", t"Sup")
    assertFailure(forallE(quantified)(r))
  }
}