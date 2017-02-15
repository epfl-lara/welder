/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.Identifier

/** Contains methods related to algebraic data types. */
trait ADTs { self: Theory =>

  import program.trees._

  /** Contains all induction hypotheses for structural induction. */
  trait StructuralInductionHypotheses {
    val constructor: Identifier
    val expression: Expr
    def hypothesis(expr: Expr): Attempt[Theorem]
    val variables: Seq[Variable]
  }

  /** Proves that a property holds on all values of a ADT by structural induction.
   *
   * @param property The property to be proven. Should be forall-quantified.
   * @param valDef   The variable definition for which the property should hold.
   *                 Its type be an ADT.
   * @param cases    Proof for each of the cases.
   * @return A forall-quantified theorem, stating that the property holds for all
   *         expressions of the given type.
   */
  def structuralInduction(property: Expr, valDef: ValDef)
      (cases: (StructuralInductionHypotheses, Goal) => Attempt[Witness]): Attempt[Theorem] = {

    forallToPredicate(property, valDef.tpe) flatMap { (f: Expr => Expr) => 
      structuralInduction(f(_), valDef)(cases)
    }
  }

  /** Proves that a property holds on all values of a ADT by structural induction.
   *
   * @param property The property to be proven.
   * @param valDef   The variable definition for which the property should hold.
   *                 Its type be an ADT.
   * @param cases    Proof for each of the cases.
   * @return A forall-quantified theorem, stating that the property holds for all
   *         expressions of the given type.
   */
  def structuralInduction(property: Expr => Expr, valDef: ValDef)
      (cases: (StructuralInductionHypotheses, Goal) => Attempt[Witness]): Attempt[Theorem] = {

    if (!valDef.tpe.isInstanceOf[ADTType]) {
      return Attempt.typeError("structuralInduction", valDef.tpe)
    }

    val tpe = valDef.tpe.asInstanceOf[ADTType]
    val p = freeze(tpe, property)

    val allCases = {

      val constructors = tpe.getADT match {
        case sort: TypedADTSort => sort.constructors
        case cons: TypedADTConstructor => Seq(cons)
      }

      constructors map { (constructor: TypedADTConstructor) =>
        val variables = constructor.fields map { (field: ValDef) =>
          val name = field.toVariable.id.name
          Variable.fresh(name, field.tpe)
        }

        val expr = ADT(constructor.toType, variables)

        (expr, variables, constructor.definition.id)
      }
    }


    val attempts = allCases map { case (expr, vars, constructorId) =>

      val variablesSet = vars.toSet

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
        val constructor = constructorId
        val expression = expr
        def hypothesis(expr: Expr) = {
          if (expr.getType == tpe && isInner(expr)) {
            Attempt.success(new Theorem(p(expr)).mark(marking))
          }
          else {
            Attempt.fail("No induction hypothesis available for " + expr + ".")
          }
        }
        val variables = vars
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

    Attempt.all(attempts) map { (theorems: Seq[Theorem]) =>
      val x = valDef.freshen
      new Theorem(Forall(Seq(x), p(x.toVariable))).from(theorems)
    }
  }
}