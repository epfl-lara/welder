/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.solvers
import inox.solvers._

/** Contains methods related to SMT solvers. */
trait Solvers { self: Theory =>

  import program.trees._

  implicit val debugSection = DebugSectionWelder

  // Factory of solvers.
  private lazy val factory = solvers.SolverFactory(program, ctx)

  private def collectConditions(expr: Expr): Seq[(Expr, Seq[Expr])] = program.symbols.collectWithPC(expr, true) {
    case (Division(lhs, rhs), path) => (not(equality(rhs, zero(rhs.getType))), path.conditions)
    case (Remainder(lhs, rhs), path) => (not(equality(rhs, zero(rhs.getType))), path.conditions)
    case (Modulo(lhs, rhs), path) => (not(equality(rhs, zero(rhs.getType))), path.conditions)
    case (FractionLiteral(_, d), path) if d == 0 => (BooleanLiteral(false), path.conditions)
  }

//  def collect(expr: Expr, assumptions: Seq[Theorem]): Seq[() => Boolean] = program.symbols.collectWithPC(expr)  {
//    case (Assume(cond, _), path) => () => checkNegationUnsat(cond, path.conditions ++ assumptions.map(_.expression))
//    case (cons@ADT(id, tps, exprs), path) if cons.getConstructor.sort.hasInvariant => {
//      val sort = cons.getConstructor.sort
//      val invariantApply = FunctionInvocation(sort.invariant.get.id, sort.tps, Seq(cons))
//      () => checkNegationUnsat(invariantApply, path.conditions ++ assumptions.map(_.expression))
//    }
//    case (Choose(vd, pred), path) => {
//      val vdFresh = vd.freshen
//      val conditions = path.conditions.map(exprOps.replaceFromSymbols(Map(vd -> vdFresh.toVariable), _))
//      val freeVars = (pred +: conditions).map(exprOps.variablesOf(_)).reduce(_ ++ _).map(_.toVal) - vd
//      // Not supported by Inox:
//      // val forall = Forall(freeVars.toSeq, implies(and(conditions : _*), not(Forall(Seq(vd), not(pred)))))
//      // () => checkNegationUnsat(forall, Seq())
//      if (freeVars.isEmpty) {
//        println(implies(and(conditions : _*), pred))
//        () => checkSat(implies(and(conditions : _*), pred))
//      }
//      else {
//        // TODO: Can we do better here ?
//        () => false
//      }
//    }
//    //    case (AsInstanceOf(expr, tpe), path) => {
//    //      () => checkNegationUnsat(IsInstanceOf(expr, tpe), path.conditions)
//    //    }
//    case (Division(lhs, rhs), path) => {
//      () => checkNegationUnsat(Not(Equals(rhs, zero(rhs.getType))), path.conditions ++ assumptions.map(_.expression))
//    }
//    case (Remainder(lhs, rhs), path) => {
//      () => checkNegationUnsat(Not(Equals(rhs, zero(rhs.getType))), path.conditions ++ assumptions.map(_.expression))
//    }
//    case (Modulo(lhs, rhs), path) => {
//      () => checkNegationUnsat(Not(Equals(rhs, zero(rhs.getType))), path.conditions ++ assumptions.map(_.expression))
//    }
//    case (FractionLiteral(_, d), _) => {
//      () => d != 0
//    }
//    // TODO: Function calls.
//  }

  private def zero(tpe: Type): Expr = tpe match {
    case IntegerType() => IntegerLiteral(0)
    case RealType() => FractionLiteral(0, 1)
    case BVType(s, n) => BVLiteral(s, 0, n)
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

    if (expr.getType != BooleanType()) {
      Attempt.typeError("prove", expr.getType)
    }
    else {
      val hypotheses = assumptions.map(_.expression)

      if (checkNegationUnsat(expr, hypotheses)) {
        val conditions = collectConditions(expr)
        val attempts = conditions.collect {
          case (condition, pathConditions) if !checkNegationUnsat(condition, pathConditions ++ hypotheses) =>
            val rest = if (pathConditions.isEmpty && hypotheses.isEmpty) "." else
              " using the following hypotheses: " + (pathConditions ++ hypotheses).mkString(", ") + "."
            Attempt.fail("SMT solver could not prove assumption " + condition + " made by expression " + expr + rest)
        }

        for {
          _ <- Attempt.all(attempts)
          t <- Attempt.success(new Theorem(expr).from(assumptions))
        } yield t
      }
      else {
        Attempt.fail("SMT solver could not prove the property: " + expr +
          ", from hypotheses: " + hypotheses.mkString(", ") + ".")
      }
    }
  }

  private def checkSat(expr: Expr): Boolean = {
    val solver = factory.getNewSolver().setTimeout(5000L)
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
    val solver = factory.getNewSolver().setTimeout(5000L)

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