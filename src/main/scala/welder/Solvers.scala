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
  
  private lazy val assumptionsCollector = CollectorWithPC(program) {
    case (Assume(cond, _), path) => () => checkNegationUnsat(cond, path.conditions)
    case (cons@ADT(adtType, exprs), path) if adtType.getADT.hasInvariant => {
      val adt = adtType.getADT
      val invariantApply = FunctionInvocation(adt.invariant.get.id, adt.tps, Seq(cons))
      () => checkNegationUnsat(invariantApply, path.conditions)
    }
    case (Choose(vd, pred), path) => {
      val vdFresh = vd.freshen
      val conditions = path.conditions.map(exprOps.replaceFromSymbols(Map(vd -> vdFresh.toVariable), _))
      val freeVars = (pred +: conditions).map(exprOps.variablesOf(_)).reduce(_ ++ _).map(_.toVal) - vd
      val forall = Forall(freeVars.toSeq, implies(and(conditions : _*), pred))
      () => checkSat(forall)
    }
    case (AsInstanceOf(expr, tpe), path) => {
      () => checkNegationUnsat(IsInstanceOf(expr, tpe), path.conditions)
    }
    case (Division(lhs, rhs), path) => {
      () => checkNegationUnsat(Not(Equals(rhs, zero(rhs.getType))), path.conditions)
    }
    case (Remainder(lhs, rhs), path) => {
      () => checkNegationUnsat(Not(Equals(rhs, zero(rhs.getType))), path.conditions)
    }
    case (Modulo(lhs, rhs), path) => {
      () => checkNegationUnsat(Not(Equals(rhs, zero(rhs.getType))), path.conditions)
    }
    case (FractionLiteral(_, d), _) => {
      () => d != 0
    }
  }

  private def zero(tpe: Type): Expr = tpe match {
    case IntegerType => IntegerLiteral(0)
    case RealType => FractionLiteral(0, 1)
    case BVType(n) => BVLiteral(0, n)
    case _ => throw new Error("zero: Not a numeric type.")
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
        for (check <- assumptionsCollector.collect(expr)) {
          if (!check()) {
            return Attempt.fail("SMT solver could not prove an assumption made by the expression " + expr + ".")
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

  private def checkSat(expr: Expr): Boolean = {
    val solver = factory.getNewSolver.setTimeout(5000L)
    try {
      solver.assertCnstr(expr)
      val result = solver.check(SolverResponses.Simple)
      println(result)
      result.isSAT
    }
    finally {
      factory.reclaim(solver)
    }
  }

  private def checkNegationUnsat(expr: Expr, assumptions: Seq[Expr]): Boolean = {
    val negation = not(implies(and(assumptions : _*), expr))
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