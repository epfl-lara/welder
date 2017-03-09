/* Copyright 2017 EPFL, Lausanne */

import inox._
import inox.trees._
import welder._

object DivisibilityExample {

  val emptyProgram = InoxProgram(Context.empty, NoSymbols)
  val theory = theoryOf(emptyProgram)
  import theory._

  // Property stating that x divides y.
  def divides(x: Expr, y: Expr): Expr = e"∃k. $x * k == $y"

  // Theorem stating that if x divides y, then x also divides any multiple of y.
  lazy val divisorMultiples =
    forallI(v"x: BigInt", v"y: BigInt") { (x: Variable, y: Variable) =>  // For any x and y.
      implI(divides(x, y)) { (xDividesY: Theorem) =>  // If x divides y.
        val (k, xTimesKisY) = xDividesY.existsE.get  // Get the value k such that x * k == y.
        forallI(v"z: BigInt") { (z: Variable) =>  // Then for any z.
          prove(e"$x * ($k * $z) == $y * $z", xTimesKisY) // Show that x * (k * z) == y * z, from the fact that x * k == y.
            .existsI(e"$k * $z", "l")  // Conclude that there exists a value l such that x * l == y * z. A witness is k * z.
        }
      }
    }

  lazy val dividesRemainder = 
    forallI(v"x: BigInt", v"y: BigInt") { (x: Variable, y: Variable) => 
      prove(e"${ divides(x, y) } == (y % x == 0)")
    }
}