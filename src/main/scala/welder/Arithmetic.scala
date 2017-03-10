/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.ast._

/** Contains methods and theorems related to arithmetic. */
trait Arithmetic { self: Theory =>
  
  import program.trees._

  def plusCommutativity(tpe: Type): Attempt[Theorem] = {
    if (numericType(tpe) == Untyped) {
      Attempt.typeError("plusCommutativity", tpe)
    } else Attempt.success {

      val a = Variable.fresh("a", tpe)
      val b = Variable.fresh("b", tpe)

      val expr = Equals(Plus(a, b), Plus(b, a))

      new Theorem(forall(Seq(a.toVal, b.toVal), expr))
    }
  }

  def plusAssociativity(tpe: Type): Attempt[Theorem] = {
    if (numericType(tpe) == Untyped) {
      Attempt.typeError("plusAssociativity", tpe)
    } else Attempt.success {

      val a = Variable.fresh("a", tpe)
      val b = Variable.fresh("b", tpe)
      val c = Variable.fresh("c", tpe)

      val expr = Equals(Plus(a, Plus(b, c)), Plus(Plus(a, b), c))

      new Theorem(forall(Seq(a.toVal, b.toVal, c.toVal), expr))
    }
  }

  def timesCommutativity(tpe: Type): Attempt[Theorem] = {
    if (numericType(tpe) == Untyped) {
      Attempt.typeError("timesCommutativity", tpe)
    } else Attempt.success {

      val a = Variable.fresh("a", tpe)
      val b = Variable.fresh("b", tpe)

      val expr = Equals(Times(a, b), Times(b, a))

      new Theorem(forall(Seq(a.toVal, b.toVal), expr))
    }
  }

  def timesAssociativity(tpe: Type): Attempt[Theorem] = {
    if (numericType(tpe) == Untyped) {
      Attempt.typeError("timesAssociativity", tpe)
    } else Attempt.success {

      val a = Variable.fresh("a", tpe)
      val b = Variable.fresh("b", tpe)
      val c = Variable.fresh("c", tpe)

      val expr = Equals(Times(a, Times(b, c)), Times(Times(a, b), c))

      new Theorem(forall(Seq(a.toVal, b.toVal, c.toVal), expr))
    }
  }

  def distributivity(tpe: Type): Attempt[Theorem] = {
    if (numericType(tpe) == Untyped) {
      Attempt.typeError("distributivity", tpe)
    } else Attempt.success {

      val a = Variable.fresh("a", tpe)
      val b = Variable.fresh("b", tpe)
      val c = Variable.fresh("c", tpe)

      val expr = Equals(Times(a, Plus(b, c)), Plus(Times(a, b), Times(a, c)))

      new Theorem(forall(Seq(a.toVal, b.toVal, c.toVal), expr))
    }
  }

  lazy val divisionDecomposition: Theorem = {
    val n = Variable.fresh("n", IntegerType)
    val d = Variable.fresh("d", IntegerType)

    new Theorem(Forall(Seq(n.toVal, d.toVal), Implies(Not(Equals(d, IntegerLiteral(0))), 
      Equals(Division(Plus(n, d), d), Plus(Division(n, d), IntegerLiteral(1)))
    )))
  }

  /** Records induction hypotheses for natural induction. */ 
  trait NaturalInductionHypotheses {

    /** The inductive variable. */
    val variable: Variable

    /** Theorem stating that the inductive variable is greater than the base case. */
    val variableGreaterThanBase: Theorem

    /** Theorem stating that the property holds for the variable. */
    val propertyForVar: Theorem

    /** Theorem stating that the property holds for the variable and all values
     *  smaller than it (but larger than the base).
     */
    val propertyForLessOrEqualToVar: Theorem
  }

  /** Tries to prove a property by natural induction.
   *
   * @param property      The property to be proved.
   * @param base          The base expression. Should be of type `IntegerType`. Typically `0` or `1`.
   * @param baseCase      Proof that the property holds in the base case.
   * @param inductiveCase Proof that the property holds in the inductive case,
   *                      assuming all induction hypotheses.
   * @return A forall-quantified theorem of the property.
   */
  def naturalInduction(property: Expr => Expr, base: Expr, baseCase: Goal => Attempt[Witness])
      (inductiveCase: (NaturalInductionHypotheses, Goal) => Attempt[Witness]): Attempt[Theorem] = {
    
    // Natural induction only works on BigInt.
    if (base.getType != IntegerType) {
      return Attempt.typeError("naturalInduction", base.getType)
    }

    // Ensures that the property function is well-behaved.
    val p = freeze(IntegerType, property)

    // Attempts to prove the base case.
    val baseProposition = p(base)
    val baseGoal = new Goal(baseProposition)
    val baseAttempt = catchFailedAttempts {
      for {
        baseWitness <- baseCase(baseGoal)
        baseTheorem <- baseWitness.extractTheorem(baseGoal)
      } yield baseTheorem
    }

    // Creates induction hypotheses.
    // Each hypothesis is marked.
    val n = Variable.fresh("n", IntegerType)
    val (greaterThanBase, m1) = new Theorem(GreaterThan(n, base)).mark
    val (propOfN, m2) = new Theorem(p(n)).mark
    val lessEqN = Variable.fresh("lessEqN", IntegerType)
    val (propLessEqN, m3) = new Theorem(Forall(Seq(lessEqN.toVal),
      Implies(And(LessEquals(lessEqN, n), GreaterEquals(lessEqN, base)), p(lessEqN)))).mark

    // Attempts to prove the inductive case.
    val inductiveAttempt = {

      // Creates the actual record to be fed to the user-specified function.
      val inductionHypotheses = new NaturalInductionHypotheses {
        val variable = n
        val variableGreaterThanBase = greaterThanBase
        val propertyForVar = propOfN
        val propertyForLessOrEqualToVar = propLessEqN
      }

      val propOfSuccN = p(Plus(n, IntegerLiteral(1)))
      val inductiveGoal = new Goal(propOfSuccN)

      catchFailedAttempts {
        for {
          inductiveWitness <- inductiveCase(inductionHypotheses, inductiveGoal)
          inductiveTheorem <- inductiveWitness.extractTheorem(inductiveGoal)
        } yield inductiveTheorem
      }
    }

    // Indicates that both the base and inductive case must succeed.
    // In which case the proof is complete and we return a theorem.
    Attempt.all(Seq(baseAttempt, inductiveAttempt)) map { case Seq(baseTheorem, inductiveTheorem) => 
      val x = Variable.fresh("n", IntegerType)
      new Theorem(Forall(Seq(x.toVal), Implies(GreaterEquals(x, base), p(x))))
        .from(baseTheorem)
        .from(inductiveTheorem)
        .unmark(m1)
        .unmark(m2)
        .unmark(m3)
    }
  }



  /** Tries to prove a property by natural induction.
   *
   * @param property      The property to be proved. Should be of the type `∀ n: BigInt. ...`.
   * @param base          The base expression. Should be of type `IntegerType`. Typically `0` or `1`.
   * @param baseCase      Proof that the property holds in the base case.
   * @param inductiveCase Proof that the property holds in the inductive case,
   *                      assuming all induction hypotheses.
   * @return A forall-quantified theorem of the property.
   */
  def naturalInduction(property: Expr, base: Expr, baseCase: Goal => Attempt[Witness])
      (inductiveCase: (NaturalInductionHypotheses, Goal) => Attempt[Witness]): Attempt[Theorem] = {

    forallToPredicate(property, IntegerType) flatMap { (f: Expr => Expr) =>
      naturalInduction(f, base, baseCase)(inductiveCase)
    }
  }
}