/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.trees._

import org.scalatest._
import Matchers._

class RelationalReasoningDSLTypingSuite extends FunSuite {

  object Empty extends Theory {
    override val program = Program(inox.trees)(NoSymbols)
    override val ctx = Context.empty
  }

  import Empty._

  val e: Expr = IntegerLiteral(1)
  val t: Theorem = truth

  test("Correct equality chains.") {
    "e ==| t | e" should compile
    "e ==| t | e ==| t | e" should compile
    "e ==| t | e ==| t | e ==| t | e" should compile
  }

  test("Incorrect equality chains.") {
    "e ==| e" shouldNot compile
    "e ==| e | e" shouldNot compile
    "e ==| t | t" shouldNot compile
    "e ==| e | t" shouldNot compile
    "t ==| t | t" shouldNot compile
    "t ==| t | e" shouldNot compile
    "t ==| e | e" shouldNot compile
    "t ==| e | t" shouldNot compile
    "e | e" shouldNot compile
    "e ==| t | e ==| e ==| t | e" shouldNot compile
  }

  test("Correct less or equal chains.") {
    "e <=| t | e" should compile
    "e ==| t | e <=| t | e" should compile
    "e <=| t | e <=| t | e" should compile
    "e <=| t | e ==| t | e" should compile
  }

  test("Correct less chains.") {
    "e <<| t | e" should compile
    "e ==| t | e <<| t | e" should compile
    "e <<| t | e <<| t | e" should compile
    "e <<| t | e ==| t | e" should compile
    "e <=| t | e <<| t | e" should compile
    "e <<| t | e <=| t | e" should compile
  }

  test("Correct greater or equal chains.") {
    "e >=| t | e" should compile
    "e ==| t | e >=| t | e" should compile
    "e >=| t | e >=| t | e" should compile
    "e >=| t | e ==| t | e" should compile
  }

  test("Correct greater chains.") {
    "e >>| t | e" should compile
    "e ==| t | e >>| t | e" should compile
    "e >>| t | e >>| t | e" should compile
    "e >>| t | e ==| t | e" should compile
    "e >=| t | e >>| t | e" should compile
    "e >>| t | e >=| t | e" should compile
  }

  test("Incorrect chains.") {
    "e >>| t | e <=| t | e" shouldNot compile
    "e >>| t | e <<| t | e" shouldNot compile
    "e >=| t | e <=| t | e" shouldNot compile
    "e >=| t | e <<| t | e" shouldNot compile
    "e <<| t | e >=| t | e" shouldNot compile
    "e <<| t | e >>| t | e" shouldNot compile
    "e <=| t | e >=| t | e" shouldNot compile
    "e <=| t | e >>| t | e" shouldNot compile
  }
}