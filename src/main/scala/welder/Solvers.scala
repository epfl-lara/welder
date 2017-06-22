/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.solvers
import inox.solvers._
import inox.transformers._

/** Contains methods related to SMT solvers. */
trait Solvers { self: Theory =>

  import program.trees._

  implicit val debugSection = DebugSectionWelder

  // Factory of solvers.
  private lazy val factory = solvers.SolverFactory.default(program)
  
  private lazy val assumeCollector = CollectorWithPC(program) {
    case (Assume(cond, _), path) => (cond, path.conditions)
    // TODO: Constructors with ADT invariants.
  }

  /** Tries to prove an expression using an SMT solver.
   *
   * @param expr The expression to be proved. Should be of type `BooleanType`.
   * @return The expression `expr` as a `Theorem`.
   */  
  def prove(expr: Expr): Attempt[Theorem] = prove(expr, Seq())

  /** Tries to prove an expression, assuming some `Theorem`s, using an SMT solver.
   *
   * @param expr  The expression to be proved. Should be of type `BooleanType`.
   * @param first The first `Theorem` used as assumption.
   * @param rest  The rest of `Theorem`s used as assumptions.
   * @return The expression `expr` as a `Theorem`.
   */ 
  def prove(expr: Expr, first: Theorem, rest: Theorem*): Attempt[Theorem] =
    prove(expr, first +: rest)

  /** Tries to prove an expression, assuming some `Theorem`s, using an SMT solver.
   *
   * @param expr        The expression to be proved. Should be of type `BooleanType`.
   * @param assumptions The list of assumptions.
   * @return The expression `expr` as a `Theorem`.
   */ 
  def prove(expr: Expr, assumptions: Seq[Theorem]): Attempt[Theorem] = {
    if (expr.getType != BooleanType) {
      Attempt.typeError("prove", expr.getType)
    }
    else {
      val hypotheses = assumptions.map(_.expression)

      if (checkNegationUnsat(expr, hypotheses)) {
        for ((cond, assumptions) <- assumeCollector.collect(expr)) {
          if (!checkNegationUnsat(cond, assumptions)) {
            return Attempt.fail("SMT solver could not prove the assumption " + cond + 
              " made by the expression " + expr +
              " given the following path conditions: " + assumptions.mkString(", ") + ".")
          }
        }

        Attempt.success(new Theorem(expr).from(assumptions))
      }
      else {
        Attempt.fail("SMT solver could not prove the property: " + expr +
          ", from hypotheses: " + hypotheses.mkString(", ") + ".")
      }
    }
  }

  private def checkNegationUnsat(expr: Expr, assumptions: Seq[Expr]): Boolean = {
    val negation = Not(Implies(and(assumptions : _*), expr))
    val solver = factory.getNewSolver.setTimeout(5000L)

    try {
        solver.assertCnstr(negation)
        val result = solver.check(SolverResponses.Simple)
        result.isUNSAT
      }
      finally {
        factory.reclaim(solver)
      }
  }
}