/* Copyright 2017 EPFL, Lausanne */

import inox._
import inox.trees._
import inox.trees.interpolator._
import welder._

object Gauss {

  // We define the sum function.
  val sumFunction: FunDef = fd"def sum(n: Integer) = if (n == 0) 0 else n + sum(n - 1)"

  // Our program simply consists of the `sum` function.
  val sumProgram: InoxProgram = Program(inox.trees)(NoSymbols.withFunctions(Seq(sumFunction)))
  val theory: Theory = theoryOf(sumProgram)
  import theory._

  // The property we want to prove, as a function of `n`.
  def property(n: Expr): Expr = {
    e"sum($n) == $n * ($n + 1) / 2"
  }

  // Call to natural induction.
  // The property we want to prove is defined just above.
  // The base expression is `0`.
  // The proof for the base case is trivial.
  val gaussTheorem: Theorem = naturalInduction(property(_), e"0", trivial) {
    case (ihs, _) =>
      // `ihs` contains induction hypotheses
      // and `goal` contains the property that needs to be proven.

      // The variable on which we induct is stored in `ihs`.
      // We bound it to `n` for clarity.
      val n = ihs.variable

      // We implicitly show that the goal is met by showing that
      // the following equalities hold. 
      e"sum($n + 1)"                    ==|
              ihs.variableGreaterThanBase |  // We use here the fact that n > 0.
      e"sum($n) + ($n + 1)"             ==|
                       ihs.propertyForVar |  // We use the induction hypothesis here.
      e"($n * ($n + 1) / 2) + ($n + 1)" ==|
                                  trivial |  // This step follows by simple arithmetic.
      e"($n + 1) * ($n + 2) / 2"
  }
}