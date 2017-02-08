/* Copyright 2017 EPFL, Lausanne */

package welder

/** Contains methods related to algebraic data types. */
trait ADTs { self: Theory =>

  import program.trees._

  /** Contains all induction hypotheses for structural induction. */
  trait StructuralInductionHypotheses {
    val expression: Expr
    def hypothesis(expr: Expr): Attempt[Theorem]
  }

  /** Proves that a property holds on all values of a given type by structural induction.
   *
   * @param property The property to be proven.
   * @param tpe      The type of expressions for which the property should hold.
   *                 Typically an `ADTType`. Also supports `TupleType`s.
   * @param cases    Proof for each of the cases.
   * @return A forall-quantified theorem, stating that the property holds for all
   *         expressions of the type `tpe`.
   */
  def structuralInduction[T <: Type](
      property: Expr => Expr,
      tpe: T,
      cases: (StructuralInductionHypotheses, Goal) => Attempt[Witness])
      (implicit fd: FinitelyDeconstructable[T]): Attempt[Theorem] = {

    val p = freeze(tpe, property)

    val attempts = fd.cases(tpe) map { case (expr, variables) =>

      val variablesSet = variables.toSet

      def isInnerOrSelf(inner: Expr): Boolean = inner == expr || isInner(inner)

      def isInner(inner: Expr): Boolean = inner match {
        case v: Variable => variablesSet.contains(v)
        case ADTSelector(adt, _) => isInnerOrSelf(adt)
        case TupleSelect(tuple, _) => isInnerOrSelf(tuple)
        case MapApply(map, _) => isInnerOrSelf(map)
        case _ => false
      }

      val marking = Mark.fresh

      val struct = new StructuralInductionHypotheses {
        val expression = expr
        def hypothesis(expr: Expr) = {
          if (expr.getType == tpe && isInner(expr)) {
            Attempt.success(new Theorem(p(expr)).mark(marking))
          }
          else {
            Attempt.fail("Could not apply induction hypothesis on " + expr)
          }
        }
      }

      val goal = new Goal(p(expr))

      cases(struct, goal) flatMap { (witness: Witness) =>
        if (!goal.accepts(witness)) {
          Attempt.incorrectWitness
        }
        else {
          Attempt.success(witness.theorem.unmark(marking))
        }
      }
    }

    if (attempts.exists(!_.isSuccessful)) {
      Attempt.fail("Some of the cases failed during structural induction.")
    }
    else {
      val theorems = attempts.map(_.get)

      val x = Variable.fresh("x", tpe)
      val conclusion = new Theorem(Forall(Seq(x.toVal), p(x))).from(theorems)

      Attempt.success(conclusion)
    }
  }
  
}