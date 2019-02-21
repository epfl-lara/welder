/* Copyright 2017 EPFL, Lausanne */

package welder

import scala.language.implicitConversions

import inox._

/** Theory over a program. */
trait Theory
  extends ADTs
     with Arithmetic
     with Evaluators
     with Paths
     with Relational
     with Rules
     with Solvers { self =>

  // Program over which theorems are stated.
  val program: InoxProgram
  val ctx: Context

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

    require(expression.getType == BooleanType())

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

    /** Conjunction elimination. */
    def andE: Attempt[Seq[Theorem]] = self.andE(this)

    /** Implication elimination. */
    def implE(proof: Goal => Attempt[Witness]): Attempt[Theorem] =
      self.implE(this)(proof)

    /** Universal quantification elimination. */
    def forallE(first: Expr, rest: Expr*): Attempt[Theorem] =
      self.forallE(this, first +: rest)

    /** Existantial quantification introduction. */
    def existsI(path: Path, name: String): Attempt[Theorem] =
      self.existsI(path, name)(this)

    /** Existantial quantification introduction. */
    def existsI(expr: Expr, name: String): Attempt[Theorem] =
      self.existsI(expr, name)(this)

    /** Existantial quantification elimination. */
    def existsE: Attempt[(Variable, Theorem)] =
      self.existsE(this)

    /** Existantial quantification elimination on n variables. */
    def existsE(n: Int): Attempt[(Seq[Variable], Theorem)] =
      if (n < 0) Attempt.fail("Illegal argument to method existsE. The parameter n is negative.")
      else if (n == 0) Attempt.success((Seq(), this))
      else for {
        vt <- self.existsE(this)
        vst <- vt._2.existsE(n - 1)
      } yield (vt._1 +: vst._1, vst._2)

    /** Disjunction elimination. */
    def orE(conclusion: Expr)(cases: (Theorem, Goal) => Attempt[Witness]): Attempt[Theorem] = 
      self.orE(this, conclusion)(cases)

    /** Negation elimination. */
    def notE: Attempt[Theorem] = self.notE(this)

//    /** Type instantiation. */
//    def instantiateType(tpeParam: TypeParameter, tpe: Type): Theorem =
//      new Theorem(symbols.instantiateType(this.expression, Map(tpeParam -> tpe))).from(this)
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
    require(expression.getType == BooleanType(), "Non-boolean expression: " + expression)

    /** Tries to satisfy the goal.
     *
     * @param theorem A `Theorem` implying the satisfaction of the goal.
     * @return A [[Witness]] object if the goal is satisfied, `None` otherwise. 
     */
    def by(theorem: Theorem): Attempt[Witness] = 
      if (theorem.expression == expression) {
        Attempt.success(new ActualWitness(new Theorem(expression).from(theorem)))
      }
      else {
        prove(expression, theorem).map(new ActualWitness(_))
      }

    /** Tries to solve the goal without any other theorems. */
    def trivial: Attempt[Witness] = by(truth)

    override def toString: String = "Goal(" + expression.toString + ")"
  }

  trait Witness {
    def extractTheorem(goal: Goal): Attempt[Theorem]
  }

  /** Witness of the satisfaction of a [[Goal]]. */
  private class ActualWitness(theorem: Theorem) extends Witness {
    override def extractTheorem(goal: Goal): Attempt[Theorem] = {
      if (goal.expression == theorem.expression) {
        Attempt.success(theorem)
      }
      else {
        Attempt.incorrectWitness
      }
    }
  }

  private class ImplicationWitness(theorem: Theorem) extends Witness {
    override def extractTheorem(goal: Goal): Attempt[Theorem] = {
      prove(goal.expression, theorem)
    }
  }

  implicit def theoremAttemptToWitnessAttempt(attempt: Attempt[Theorem]): Attempt[Witness] =
    attempt.map(new ImplicationWitness(_))

  implicit def theoremToWitnessAttempt(theorem: Theorem): Attempt[Witness] =
    Attempt.success(new ImplicationWitness(theorem))

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

    import ctx.reporter._

    (x: Expr) => {
      val a = exprOps.replaceFromSymbols(Map(hole -> x), expr)

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

  /** Represents possibly failing computations.
   *
   * In case of non-successful attempts, returns the reasons of failure.
   */ 
  sealed abstract class Attempt[+A] {

    /** Applies a function to the value in case of a successful attempt. */
    def map[B](f: A => B): Attempt[B] = this match {
      case Success(x) => Success(f(x))
      case Failure(msg) => Failure(msg)
    }

    /** Applies a function to the value in case of a successful attempt. */
    def flatMap[B](f: A => Attempt[B]) = this match {
      case Success(x) => f(x)
      case Failure(msg) => Failure(msg)
    }

    /** Checks if the attempt is successful. */
    def isSuccessful: Boolean = this match {
      case Success(_) => true
      case _          => false 
    }

    /** Specifies an alternative in case `this` attempt fails. */
    def orElse[B >: A](alternative: => Attempt[B]): Attempt[B] = this match {
      case Success(_) => this
      case Failure(_) => Attempt.atLeastOne(Seq(this, alternative))
                          .map((xs: Seq[B]) => xs.head)
    }

    /** Gets the successful value.
     *
     * Throws an exception when applied on an unsuccessful attempt.
     */
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

  private[welder] def catchFailedAttempts[A](attempt: => Attempt[A]): Attempt[A] = {
    try {
      attempt
    }
    catch {
      case AttemptException(reason) => Failure(reason)
    }
  }

  case class AttemptException(reason: FailureReason) extends Exception(reason.toString)

  implicit def valueToAttempt[A](value: A): Attempt[A] = Attempt.success(value)

  implicit def attemptToValue[A](attempt: Attempt[A]): A = attempt match {
    case Success(x) => x
    case Failure(reason) => throw AttemptException(reason)
  }


  def forallToPredicate(x: Expr, tpe: Type): Attempt[Expr => Expr] = x match {
    case Forall(Seq(n), e) if n.tpe == tpe => Attempt.success { expr: Expr =>
      exprOps.replaceFromSymbols(Map(n -> expr), e)
    }
    case Forall(ns, e) if ns(0).tpe == tpe => Attempt.success { expr: Expr =>
      exprOps.replaceFromSymbols(Map(ns(0) -> expr), Forall(ns.tail, e))
    }
    case _ => Attempt.fail("Could not transform expression into predicate.")
  }

  /** States that the goal can be trivially proven. */
  object trivial extends Success[Witness](new ImplicationWitness(truth))
                    with (Goal => Attempt[Witness])
                    with ((Theorem, Goal) => Attempt[Witness]) {

    override def apply(goal: Goal): Attempt[Witness] = goal.trivial
    override def apply(theorem: Theorem, goal: Goal): Attempt[Witness] = {
      goal.by(theorem)
    }
  }
}