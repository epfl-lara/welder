/* Copyright 2017 EPFL, Lausanne */

package welder

import scala.language.implicitConversions

import inox._
import inox.trees._

/** Theory over a program. */
trait Theory
  extends ADTs
     with Arithmetic
     with Equational
     with Evaluators
     with Paths
     with Rules
     with Solvers { self =>

  // Program over which theorems are stated.
  val program: InoxProgram

  import program.trees._
  implicit lazy val symbols = program.symbols

  /** Wrapper around provable expressions.
   *
   * `Theorem`s are wrappers around expressions of type `BooleanType`.
   * Users of the library can not build `Theorem`s using the constructor directly.
   * Instead, they must rely on the combinators provided by the various mixed-in traits.
   *
   * @constructor Asserts the expression as true, in some scope.
   * @param expression The expression which is stated to hold.
   * @param markings   A set of markings, indicating in which scopes this theorem is valid.
   *                   An empty set indicates that this theorem is valid in the global scope.
   */
  class Theorem private[welder] (val expression: Expr, 
      private[welder] val markings: Set[Mark] = Set()) {

    require(expression.getType == BooleanType)

    /** Mark this Theorem with a fresh marking.
     *
     * This is used to indicate that the Theorem is valid
     * in a limited scope.
     */
    private[welder] def mark: (Theorem, Mark) = {
      val marking = Mark.fresh

      (new Theorem(expression, markings + marking), marking)
    }

    /** Mark this Theorem with the provided marking.
     *
     * This is used to indicate that the Theorem is valid
     * in a limited scope.
     */
    private[welder] def mark(marking: Mark): Theorem = {
      new Theorem(expression, markings + marking)
    }

    /** Removes a marking from this Theorem. */
    private[welder] def unmark(marking: Mark): Theorem = {
      new Theorem(expression, markings - marking)
    }

    /** Removes a set of markings from this Theorem. */
    private[welder] def unmark(markings: Seq[Mark]): Theorem = {
      new Theorem(expression, this.markings -- markings)
    }

    /** Indicate that this Theorem is derived from another Theorem.
     *
     * The resulting Theorem is additionally marked by all markings of the other Theorem.
     */
    private[welder] def from(that: Theorem): Theorem = new Theorem(expression, markings ++ that.markings)

    /** Indicate that this Theorem is derived from others Theorems.
     *
     * The resulting Theorem is additionally marked by all markings of the other Theorems.
     */
    private[welder] def from(those: Seq[Theorem]): Theorem = {
      if (those.isEmpty) {
        this
      }
      else {
        new Theorem(expression, markings ++ those.map(_.markings).reduce(_ ++ _))
      }
    }

    override def toString(): String = 
      "Theorem" + (if (isGloballyValid) "" else "*") + "(" + expression.toString() + ")"

    /** Checks if this `Theorem` is valid in the global scope. */
    def isGloballyValid: Boolean = markings.isEmpty


    def andE: Attempt[Seq[Theorem]] = self.andE(this)
    def implE(proof: Goal => Attempt[Witness]): Attempt[Theorem] = self.implE(this)(proof)
    def forallE(first: Expr, rest: Expr*): Attempt[Theorem] = self.forallE(this, first +: rest)
    def orE(conclusion: Expr)(cases: (Theorem, Goal) => Attempt[Witness]): Attempt[Theorem] = self.orE(this, conclusion)(cases)
    def notE: Attempt[Theorem] = self.notE(this)
  }

  /** Markings, used to taint Theorems that are valid only in a specific scope. */
  private[welder] type Mark = BigInt

  /** Generator of fresh markings. */
  private[welder] object Mark {

    /** Holds the next value returned by fresh. */
    private var nextFresh: Mark = 0

    /** Returns a fresh marking. */
    def fresh: Mark = synchronized {
      val ret = nextFresh
      nextFresh += 1
      ret
    }
  }

  /** States a goal, in the form of an expression to be proved. */
  class Goal(val expression: Expr) { 
    require(expression.getType == BooleanType, "Non-boolean expression: " + expression)

    /** Tries to satisfy the goal.
     *
     * @param theorem A `Theorem` implying the satisfaction of the goal.
     * @return A [[Witness]] object if the goal is satisfied, `None` otherwise. 
     */
    def by(theorem: Theorem): Attempt[Witness] = 
      if (theorem.expression == expression) {
        Attempt.success(new Witness(new Theorem(expression).from(theorem)))
      }
      else {
        // Do we really want to invoke the solver in this case ?
        prove(expression, theorem).map(new Witness(_))
      }

    /** Tries to solve the goal without any other theorems. */
    def trivial: Attempt[Witness] = by(truth)

    /** Verifies that the [[Witness]] is accepted. */
    private[welder] def accepts(witness: Witness): Boolean =
      expression == witness.theorem.expression

    override def toString: String = "Goal(" + expression.toString + ")"
  }

  /** Witness of the satisfaction of a [[Goal]]. */
  class Witness private[welder] (val theorem: Theorem)

  /** Turns any function `f: Expr => Expr` into an ''expression context''.
   *
   * This works by applying the function `f` to a fresh variable, and so only once.
   * Application of the resulting function is then resolved using variable substitution.
   *
   * This function is used to ensure that functions passed by users to the various
   * combinators have nice properties, such as congruency `(a == b ==> f(a) == f(b))`.
   *
   * @param tpe The type of the expression argument expected by `f`.
   * @param f   The function to "freeze".
   */
  private[welder] def freeze(tpe: Type, f: Expr => Expr): Expr => Expr = {
    val hole = Variable.fresh("hole", tpe)
    val expr = f(hole)

    import program.ctx.reporter._

    (x: Expr) => {
      val a = exprOps.replaceFromSymbols(Map((hole -> x)), expr)

      if (isDebugEnabled(DebugSectionWelder)) {
        val b = f(x)

        if (a != b) {
          warning("Function does not behave as a context.")
        }
      }

      a
    }
  }

  sealed abstract class FailureReason(val reason: String) {
    val underlying: Seq[FailureReason] = Seq()
  }
  case object IncorrectWitness extends FailureReason("Returned an incorrect witness.")
  case class TypeError(name: String, tpe: Type)
    extends FailureReason("Operation " + name + " not supported for type " + tpe + ".")
  case class Unspecified(text: String) extends FailureReason(text)
  case class Aborted(text: String) extends FailureReason(text)
  case class AllOfFailureReasons(reasons: Seq[FailureReason])
    extends FailureReason("Failed due to multiple reasons: ") {

    override val underlying = reasons
  }
  case class OneOfFailureReasons(reasons: Seq[FailureReason])
    extends FailureReason("Failed due to one of the following reasons: ") {

    override val underlying = reasons
  }


  // TODO: Record counter-examples.
  // TODO: Record multiple failed attempts.
  sealed abstract class Attempt[+A] {
    def map[B](f: A => B): Attempt[B] = this match {
      case Success(x) => Success(f(x))
      case Failure(msg) => Failure(msg)
    }

    def flatMap[B](f: A => Attempt[B]) = this match {
      case Success(x) => f(x)
      case Failure(msg) => Failure(msg)
    }

    def isSuccessful: Boolean = this match {
      case Success(_) => true
      case _          => false 
    }

    def get: A = attemptToValue(this)
  }
  case class Success[A](value: A) extends Attempt[A]
  case class Failure(reason: FailureReason) extends Attempt[Nothing]

  object Attempt {
    def fail(msg: String) = Failure(Unspecified(msg))
    def abort(msg: String) = Failure(Aborted(msg))
    def typeError(operation: String, tpe: Type) = Failure(TypeError(operation, tpe))
    def incorrectWitness = Failure(IncorrectWitness)
    def success[A](x: A) = Success(x)

    def all[A](as: Seq[Attempt[A]]): Attempt[Seq[A]] = {
      if (as.exists(!_.isSuccessful)) {
        Failure(AllOfFailureReasons(as.collect {
          case Failure(reason) => reason
        }))
      }
      else {
        Success(as.map(_.get))
      }
    }

    def atLeastOne[A](as: Seq[Attempt[A]]): Attempt[Seq[A]] = {
      if (!as.exists(_.isSuccessful)) {
        Failure(OneOfFailureReasons(as.collect {
          case Failure(reason) => reason
        }))
      }
      else {
        Success(as.collect {
          case Success(v) => v
        })
      }
    }
  }

  implicit def valueToAttempt[A](value: A): Attempt[A] = Attempt.success(value)

  implicit def attemptToValue[A](attempt: Attempt[A]): A = attempt match {
    case Success(x) => x
    case Failure(msg) => program.ctx.reporter.fatalError(msg)
  }


  def forallToPredicate(x: Expr, tpe: Type): Attempt[Expr => Expr] = x match {
    case Forall(Seq(n), e) if n.tpe == tpe => Attempt.success { (expr: Expr) => 
      exprOps.replaceFromSymbols(Map((n -> expr)), e)
    }
    case Forall(ns, e) if ns(0).tpe == tpe => Attempt.success { (expr: Expr) => 
      exprOps.replaceFromSymbols(Map((ns(0) -> expr)), Forall(ns.tail, e))
    }
    case _ => Attempt.fail("Could not transform expression into predicate.")
  }
}