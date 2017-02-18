/* Copyright 2017 EPFL, Lausanne */

import inox._
import inox.trees._
import inox.trees.dsl._
import welder._

object GaussExample {

  // We create an identifier for the function.
  val sum = FreshIdentifier("sum")

  // We define the sum function.
  val sumFunction = mkFunDef(sum)() { case _ =>

    // The function takes only one argument, of type `BigInt`.
    val args: Seq[ValDef] = Seq("n" :: IntegerType)

    // It returns a `BigInt`.
    val retType: Type = IntegerType

    // Its body is defined as:
    val body: Seq[Variable] => Expr = { case Seq(n) =>
      if_ (n === E(BigInt(0))) {
        // We return `0` if the argument is `0`.
        E(BigInt(0))
      } else_ {
        // We call the function recursively on `n - 1` in other cases.
        val predN = n - E(BigInt(1))     
        E(sum)(predN) + n
      }
    }

    (args, retType, body)
  }

  // Our program simply consists of the `sum` function.
  val sumProgram = InoxProgram(Context.empty,
                     NoSymbols.withFunctions(Seq(sumFunction)))
  val theory = theoryOf(sumProgram)
  import theory._

  // The property we want to prove, as a function of `n`.
  def property(n: Expr): Expr = {
    e"sum($n) == $n * ($n + 1) / 2"
  }

  // Call to natural induction.
  // The property we want to prove is defined just above.
  // The base expression is `0`.
  // The proof for the base case is trivial.
  val gaussTheorem = naturalInduction(property(_), e"0", trivial) { 
    case (ihs, goal) =>
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