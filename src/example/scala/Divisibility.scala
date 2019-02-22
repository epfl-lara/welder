/* Copyright 2017 EPFL, Lausanne */

import inox._
import inox.trees._
import inox.trees.interpolator._
import welder._

object Divisibility {

  val emptyProgram: InoxProgram = Program(inox.trees)(NoSymbols)
  val theory: Theory = theoryOf(emptyProgram)
  import theory._

  // Property stating that x divides y.
  def divides(x: Expr, y: Expr): Expr = e"!forall k => $x * k != $y"

  // Theorem stating that if x divides y, then x also divides any multiple of y.
  lazy val divisorMultiples: Theorem =
    forallI(vd"x: Integer", vd"y: Integer") { (x: Variable, y: Variable) =>  // For any x and y.
      implI(divides(x, y)) { xDividesY: Theorem =>  // If x divides y.
        val (k, xTimesKisY) = xDividesY.existsE.get  // Get the value k such that x * k == y.
        forallI(vd"z: Integer") { z: Variable =>  // Then for any z.
          prove(e"$x * ($k * $z) == $y * $z", xTimesKisY) // Show that x * (k * z) == y * z, from the fact that x * k == y.
            .existsI(e"$k * $z", "l")  // Conclude that there exists a value l such that x * l == y * z. A witness is k * z.
        }
      }
    }

  // The quotient-remainder theorem, stating that, for any a and b, there exists q and r such that a = q * b + r.
  lazy val quotientRemainder: Theorem = forallI(vd"a: Integer", vd"b: Integer") { (a: Variable, b: Variable) =>
    implI(e"$b != 0") { bNonZero: Theorem =>
      val q = e"$a / $b"
      val r = e"$a % $b"
      prove(e"$a == $q * $b + $r", bNonZero)
        .existsI(e"$q", "q")
        .existsI(e"$r", "r")
    }
  }

  // Theorem relating the integer division and remainder operations.
  lazy val remainderDefinition: Theorem = forallI(vd"n: Integer", vd"m: Integer") { (n: Variable, m: Variable) =>
    implI(e"$m != 0") { mPositive: Theorem =>
      prove(e"$n % $m == $n - ($n / $m) * $m", mPositive)
    }
  }

  // Theorem stating that, for any x != 0 and n, (x * n) / x == n.
  lazy val wholeDivision: Theorem = forallI(vd"x: Integer") { x: Variable =>
    implI(e"$x != 0") { xNonZero: Theorem =>

      // We first state the theorem for all n >= 0.
      val nPos = {
        def property(k: Expr) = e"($x * $k) / $x == $k"

        // We prove this by induction.
        naturalInduction(property(_), e"0", _.by(xNonZero)) { case (ihs, goal) =>

          val n = ihs.variable

          // We apply the axiom about division on x * n and x.
          val oneStep = divisionDecomposition
            .forallE(e"$x * $n", e"$x")
            .implE(_.by(xNonZero))

          // The inductive case is derived from:
          val equality =
            e"($x * ($n + 1)) / $x"            ==|
                                        xNonZero |
            e"($x * $n + $x) / $x"             ==|
                         andI(xNonZero, oneStep) |
            e"($x * $n) / $x + 1"              ==|
              andI(xNonZero, ihs.propertyForVar) |
            e"$n + 1"

          andI(equality, xNonZero)
        }
      }

      // We then state the theorem for negative n's.
      val nNeg = {
        forallI(vd"n: Integer") { n: Variable =>
          implI(e"$n < 0") { nNeg: Theorem =>

            // We apply the theorem for -n, since -n is positive.
            val lemma = nPos.forallE(e"-$n").implE(_.by(nNeg))

            // The following derivation shows
            // that the property holds also for negative n's:
            e"($x * $n) / $x"     ==|
                           xNonZero |
            e"-($x * -$n) / $x"   ==|
                           xNonZero |
            e"-(($x * -$n) / $x)" ==|
              andI(xNonZero, lemma) |
            e"-(-$n)"             ==|
                            trivial |
            e"$n"

          }
        }
      }

      // Then, we can finally state the theorem for an arbitrary n.
      forallI(vd"n: Integer") { n: Variable =>

        // We have that n is either negative or positive.
        val nEitherPosOrNeg = prove(e"$n < 0 || $n >= 0")

        // Prove the property on n by case analysis on the above disjunction.
        nEitherPosOrNeg.orE(e"($x * $n) / $x == $n") {

          // In the case when we know that n is negative...
          case (thm, goal) if thm.expression == e"$n < 0" =>

            // We apply the nNeg lemma.
            goal.by(andI(nNeg.forallE(e"$n").implE(_.by(thm)), xNonZero))

          // In the case when we know that n is positive...
          case (thm, goal) if thm.expression == e"$n >= 0" =>

            // We apply the nPos lemma.
            goal.by(andI(nPos.forallE(e"$n").implE(_.by(thm)), xNonZero))
        }
      }
    }
  }


  // Theorem stating that, for any non-zero x and arbitrary y,
  // x divides y if and only if the remainder of the division by x of y is zero. 
  lazy val dividesRemainder: Theorem =
    forallI(vd"x: Integer", vd"y: Integer") { (x: Variable, y: Variable) =>
      implI(e"$x != 0") { xNonZero: Theorem =>

        // First direction. We assume that x divides y.
        val dir1 = implI(divides(x, y)) { xDividesY: Theorem =>
          val (k, xTimesKisY) = xDividesY.existsE.get

          // We apply the lemma about whole division to x and k.
          val lemmaWholeDiv = wholeDivision
            .forallE(e"$x")
            .implE(_.by(xNonZero))
            .forallE(e"$k")

          // We derive that y % x == 0.
          e"$y % $x"                          ==|
            andI(xNonZero, remainderDefinition) |
          e"$y - ($y / $x) * $x"              ==|
                     andI(xNonZero, xTimesKisY) |
          e"$y - (($x * $k) / $x) * $x"       ==|
                  andI(xNonZero, lemmaWholeDiv) |
          e"$y - $k * $x"                     ==|
                                     xTimesKisY |
          e"$y - $y"                          ==|
                                        trivial |
          e"0"
        }

        // Second direction. We assume that y % x = 0.
        val dir2 = implI(e"$y % $x == 0") { remainderZero: Theorem =>
          val lemma =
            e"$y - ($y / $x) * $x"              ==|
              andI(xNonZero, remainderDefinition) |
            e"$y % $x"                          ==|
                    andI(xNonZero, remainderZero) |
            e"0"

          prove(e"$x * ($y / $x) == $y", andI(lemma, xNonZero))
            .existsI(e"$y / $x", "k")
        }

        // Combine the two directions to show the equivalence between the two statements.
        iffI(divides(x, y), e"$y % $x == 0", {
          case (thm, goal) => goal.by(dir1.implE(_.by(thm)))
        }, {
          case (thm, goal) => goal.by(dir2.implE(_.by(thm)))
        })
      }
    }
}
