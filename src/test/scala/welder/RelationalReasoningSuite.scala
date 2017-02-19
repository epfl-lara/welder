/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.trees._

import org.scalatest._

class RelationalReasoningSuite extends FunSuite {

  object Empty extends Theory {
    override val program = InoxProgram(Context.empty, NoSymbols)
  }

  import Empty._
  import relations._

  def assertSuccessful(attempt: => Attempt[_]) {
    assert(attempt.isSuccessful)
  }

  def viaSMT(label: String, expression: Expr) {
    test(label) {
      assertSuccessful {
        prove(expression)
      }
    }
  }

  // Checking that the SMT solver can indeed prove the transitivity of the relations.
  val rels = Seq(EQ, LT, LE, GT, GE)  // All relations.
  val tpes = Seq(CharType, IntegerType, Int32Type, RealType)  // Types which support the relations.
  for (tpe <- tpes; rel1 <- rels; rel2 <- rels) compose(rel1, rel2) match {
    case Some(rel12) => viaSMT("Relation " + rel1 + " followed by " + rel2 + " (" + tpe + ")", {
      val a = Variable.fresh("a", tpe)
      val b = Variable.fresh("b", tpe)
      val c = Variable.fresh("c", tpe) 

      Implies(And(rel1(a, b), rel2(b, c)), rel12(a, c))
    })
    case None => ()
  }  

  for (tpe <- tpes; rel1 <- rels; rel2 <- rels) compose(rel1, rel2) match {
    case Some(rel12) => {
      val a = Variable.fresh("a", tpe)
      val b = Variable.fresh("b", tpe)
      val c = Variable.fresh("c", tpe) 

      val acNotEqual = prove(Implies(And(rel1(a, b), rel2(b, c)), Not(Equals(a, c))))

      if (acNotEqual.isSuccessful) {
        // Able to prove that a and c are not equal.

        viaSMT("Relation " + rel1 + " followed by " + rel2 + " preserves inequality (" + tpe + ")",
          Implies(rel12(a, c), Not(Equals(a, c))))
      }
      else {
        // Not able to prove that a and c are not equal.
        // So... a and c should be equal.

        viaSMT("Relation " + rel1 + " followed by " + rel2 + " preserves equality (" + tpe + ")",
          Implies(Equals(a, c), rel12(a, c)))
      }
    }
    case None => ()
  }
}