/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.solvers
import inox.solvers._

/** Contains methods related to SMT solvers. */
trait Solvers { self: Theory =>

  import program.trees._

  implicit val debugSection = DebugSectionWelder

  // Factory of solvers.
  private lazy val factory = solvers.SolverFactory.default(program)
  
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
      val negation = Not(Implies(and(hypotheses : _*), expr))

      program.ctx.reporter.debug(negation)

      val solver = factory.getNewSolver.setTimeout(60000L)
      solver.assertCnstr(negation)
      val result = solver.check(SolverResponses.Model) // TODO: What to do with models?

      program.ctx.reporter.debug(result)

      if (result.isUNSAT) {
        // Impossible to satisfy the negation of the expression,
        // thus the expression follows from the assumptions.
        Attempt.success(new Theorem(expr).from(assumptions))
      }
      else {
        Attempt.fail("SMT solver could not prove the property.")
      }
    }
  }
}