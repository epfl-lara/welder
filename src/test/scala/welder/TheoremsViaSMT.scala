/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.trees._

import org.scalatest._

class TheoremsViaSMTSuite extends FunSuite {

  object Empty extends Theory {
    override val program = InoxProgram(Context.empty, NoSymbols)
  }

  import Empty._

  def assertSuccessful(attempt: => Attempt[_]) {
    assert(attempt.isSuccessful)
  }

  def viaSMT(label: String, theorem: Theorem) {
    test(label) {
      assertSuccessful {
        prove(theorem.expression)
      }
    }
  }

  viaSMT("Truth", truth)
  viaSMT("Excluded Middle", excludedMiddle)
  viaSMT("Implication Elimination", implE)
  viaSMT("Negation Introduction", notI)
  viaSMT("Negation Elimination", notE)
  viaSMT("Iff Introduction", iffI)
  viaSMT("Iff Elimination", iffE)

  def viaSMT(label: String, attempt: Type => Attempt[Theorem], tpe: Type) {
    test(label + " (" + tpe + ")") {
      assertSuccessful {
        attempt(tpe) flatMap { (theorem: Theorem) =>
          prove(theorem.expression)
        }
      }
    }
  }

  val numericTypes = Seq(IntegerType, Int32Type, RealType)
  val types = numericTypes ++ Seq(BooleanType, StringType, CharType, UnitType, FunctionType(Seq(IntegerType), IntegerType))

  for (tpe <- types) viaSMT("Reflexivity of Equality", reflexivity, tpe)
  for (tpe <- types) viaSMT("Symmetry of Equality", symmetry, tpe)
  for (tpe <- numericTypes) viaSMT("Commutativity of Addition", plusCommutativity, tpe)
  for (tpe <- numericTypes) viaSMT("Associativity of Addition", plusAssociativity, tpe)
  for (tpe <- numericTypes) viaSMT("Commutativity of Multiplication", timesCommutativity, tpe)
  for (tpe <- numericTypes) viaSMT("Associativity of Multiplication", timesAssociativity, tpe)
  for (tpe <- numericTypes) viaSMT("Distributivity of Multiplication over Addition", distributivity, tpe)
}