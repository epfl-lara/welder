
package welder

import inox._
import inox.evaluators._

/** Contains methods related to the use of evaluation. */
trait Evaluators { self: Theory =>

  import program.trees._
  
  // The evaluator.
  private lazy val evaluator: DeterministicEvaluator { val program: InoxProgram } = {
    val program = self.program
    RecursiveEvaluator.default(program)
  }

  /** Returns a `Theorem` stating the equality of
   *  the given expression and its evaluated form.
   *
   * @param expr The expression to evaluate.
   * @return The proven equality between `expr` and its evaluated form.
   */
  def evaluated(expr: Expr): Attempt[Theorem] = {

    val result = evaluator.eval(expr)

    result.result match {
      case Some(value) => Attempt.success(new Theorem(Equals(expr, value)))
      case None        => Attempt.fail("Could not evaluate expression " + expr + " correctly.")
    }
  }

  /** Returns the given theorem with the specified part evaluated.
   *
   * @param theorem A proven statement.
   * @param path    Which part of the statement to evaluate.
   * @return The `theorem` with the part specified by the `path` evaluated.
   */
  def evaluated(theorem: Theorem, path: Path): Attempt[Theorem] = {

    val expr = theorem.expression
    val focuses = path.on(expr)

    if (focuses.isEmpty) {
      // No expression satisfying path.
      return Attempt.fail("No expression satisfying the provided path.")
    }
    if (!focuses.tail.isEmpty) {
      // Ambiguity here.
      return Attempt.fail("Path is ambiguous.")
    }

    val focus = focuses.head
    val original = focus.get

    val result = evaluator.eval(original)

    result.result match {
      case Some(value) => Attempt.success(new Theorem(focus.set(value)).from(theorem))
      case None        => Attempt.fail("Could not evaluate expression " + expr + " correctly.")
    }
  }
}