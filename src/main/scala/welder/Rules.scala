/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.ast._

/** Contains introduction and elimination rules for many constructions. */
trait Rules { self: Theory =>
  import program.trees._

  def notI(hypothesis: Expr)
          (contradiction: (Theorem, Goal) => Attempt[Witness]): Attempt[Theorem] = {

    val (hyp, mark) = new Theorem(hypothesis).mark
    val goal = new Goal(BooleanLiteral(false))
    contradiction(hyp, goal) flatMap { (witness: Witness) =>
      if (goal.accepts(witness)) {
        Attempt.success(new Theorem(Not(hypothesis)).from(witness.theorem).unmark(mark))
      }
      else {
        Attempt.incorrectWitness
      }
    }
  }

  /** Negation introduction.
   *
   * Contains the `Theorem` : `∀x. (x → false) → ¬x`.
   */
  lazy val notI: Theorem = {
    val x = Variable.fresh("x", BooleanType)
    val expr = Implies(Implies(x, BooleanLiteral(false)), Not(x))

    new Theorem(Forall(Seq(x.toVal), expr))
  }
    
  /** Removes a top level double negation.
   *
   * @param thm A `Theorem` of the form `Not(Not(expr))`.
   * @return The `Theorem` `expr`.
   */
  def notE(thm: Theorem): Attempt[Theorem] =
    thm.expression match {
      case Not(Not(expression)) => Attempt.success(new Theorem(expression).from(thm))
      case _ => Attempt.fail("Impossible to apply the rule notE on " + thm.expression)
    }

  /** Negation elimination.
   *
   * Contains the `Theorem` : `∀x. ¬¬x = x`.
   */
  lazy val notE: Theorem = {
    val x = Variable.fresh("x", BooleanType)
    val expr = Equals(Not(Not(x)), x)

    new Theorem(Forall(Seq(x.toVal), expr))
  }

  /** Given a sequence of `Theorem`s, proves their conjunctions.
   *
   * @param theorems A sequence of theorems.
   * @return A theorem for the conjunction of theorems.
   */
  def andI(theorems: Seq[Theorem]): Theorem = theorems match {
    case Seq() => truth
    case Seq(theorem) => theorem
    case _ => new Theorem(And(theorems.map(_.expression))).from(theorems)
  }

  /** Given a sequence of `Theorem`s, proves their conjunctions.
   *
   * @param first First theorem of the sequence.
   * @param rest  The rest of the theorems.
   * @return A theorem for the conjunction of theorems.
   */
  def andI(first: Theorem, rest: Theorem*): Theorem = andI(first +: rest)

  /** Given a `Theorem` in the form of a conjunction, returns a theorem for each conjunct.
   *
   * @param conjunction A proven conjunction.
   * @return A sequence of proven conjuncts.
   */
  def andE(conjunction: Theorem): Attempt[Seq[Theorem]] = conjunction.expression match {
    case And(expressions) => Attempt.success(expressions.map(new Theorem(_).from(conjunction)))
    case _ => Attempt.fail("Can not apply the rule andE on non-conjunction expression " + conjunction)
  }

  /** Proves the disjunction of a sequence of expressions by proving at least one of the cases.
   *
   * @param expressions The disjuncts.
   * @param cases       Proof function, applied to each disjunct separately.
   * @return A `Theorem` for the disjunction.
   */
  def orI(expressions: Seq[Expr])(cases: Goal => Attempt[Witness]): Attempt[Theorem] = {
    val attempts = expressions.map { (expr: Expr) =>
      val goal = new Goal(expr)
      cases(goal) flatMap { (witness: Witness) =>
        if (goal.accepts(witness)) {
          Attempt.success(witness.theorem)
        }
        else {
          Attempt.incorrectWitness
        }
      }
    }

    if (!attempts.exists(_.isSuccessful)) {
      Attempt.fail("Not a single case could be proven.")
    }
    else {
      val successfulTheorems = attempts.filter(_.isSuccessful).map(_.get)

      Attempt.success(new Theorem(Or(expressions)).from(successfulTheorems))
    }
  } 

  /** Proves an expression using case analysis on a proven disjunction.
   *
   * @param disjunction A proven disjunction.
   * @param conclusion  An expression to be proved.
   * @param cases       A proof function, called once for each disjunct.
   * @return A theorem for the `conclusion`. 
   */
  def orE(disjunction: Theorem, conclusion: Expr)(cases: (Theorem, Goal) => Attempt[Witness]): Attempt[Theorem] =
    disjunction.expression match {
      case Or(alternatives) => {
        val attempts = alternatives.map { (expr: Expr) =>
          val (hyp, mark) = new Theorem(expr).mark
          val goal = new Goal(conclusion)

          cases(hyp, goal) flatMap { (witness: Witness) =>
            if (goal.accepts(witness)) {
              Attempt.success(witness.theorem.unmark(mark))
            }
            else {
              Attempt.incorrectWitness
            }
          }
        }

        if (attempts.exists(!_.isSuccessful)) {
          Attempt.fail("Could not prove all cases in orE.")
        }
        else {
          Attempt.success(new Theorem(conclusion).from(attempts.map(_.get)))
        }
      }
      case _ => Attempt.fail("Can not apply rule orE on non-disjunction expression " + disjunction.expression + ".")
    }

  def orToImpl(disjunction: Theorem): Attempt[Seq[Theorem]] = disjunction.expression match {
    case Or(expressions) =>
      Attempt.success {
        Utils.oneHole(expressions) map {
          case (x, xs) => new Theorem(Implies(not(or(xs : _*)), x)).from(disjunction)
        }
      }
    case _ => Attempt.fail("Can not apply rule orToImpl on non-disjunction expression " + disjunction.expression + ".")
  }

  /** Implication introduction.
   *
   * Proves that `assumption` implies a conclusion by proving that the conclusion holds
   * assuming the `assumption`.
   *
   * @param assumption An expression to assume. Should be of type `BooleanType`.
   * @param conclusion The derivation of a `Theorem`, assuming the `assumption`.
   * @return A `Theorem` of the implication, or `None`. 
   */
  def implI(assumption: Expr)(conclusion: Theorem => Attempt[Theorem]): Attempt[Theorem] = {
    
    if (assumption.getType != BooleanLiteral) {
      return Attempt.fail("Passed non-boolean expression " + assumption + " to implI.")
    }

    val (hypothesis, mark) = new Theorem(assumption).mark

    conclusion(hypothesis) map {
      (thm: Theorem) => new Theorem(Implies(assumption, thm.expression)).from(thm).unmark(mark)
    }
  }

  /** Implication elimination.
   *
   * Contains the `Theorem` : `∀x y. ((x → y) ∧ x) → y`.
   */
  lazy val implE: Theorem = {
    val x = Variable.fresh("x", BooleanType)
    val y = Variable.fresh("y", BooleanType)
    val expr = Implies(And(Implies(x, y), x), y)

    new Theorem(Forall(Seq(x.toVal, y.toVal), expr))
  }

  def implE(implication: Theorem)(proof: Goal => Attempt[Witness]): Attempt[Theorem] = 
    implication.expression match {
      case Implies(condition, body) => {
        val goal = new Goal(condition)

        proof(goal) flatMap { (witness: Witness) =>
          if (goal.accepts(witness)) {
            Attempt.success(new Theorem(body).from(witness.theorem))
          }
          else {
            Attempt.incorrectWitness
          }
        }
      } 
      case _ => Attempt.fail("Could not apply rule implE on non-implication expression " + implication.expression + ".")
    }

  def forallI(tpe: Type, theorem: Theorem): Theorem = {
    val x = Variable.fresh("x", tpe)

    new Theorem(Forall(Seq(x.toVal), theorem.expression)).from(theorem)
  }

  def forallE(quantified: Theorem)(first: Expr, rest: Expr*): Attempt[Theorem] = forallE(quantified, first +: rest)

  def forallE(quantified: Theorem, terms: Seq[Expr]): Attempt[Theorem] = quantified.expression match {
    case Forall(defs, expression) if terms.size == defs.size => {

      val substitutions = defs.zip(terms).toMap

      val typeError = substitutions.exists { case (vd, e) =>
        vd.getType != e.getType || e.getType == Untyped
      }

      if (typeError) {
        Attempt.fail("Some arguments to forallE have incorrect types.")
      }
      else {
        // TODO: Check that no problem arises due to shared identifiers.

        Attempt.success(new Theorem(exprOps.replaceFromSymbols(substitutions, expression)).from(quantified))
      }
    }
    case _ => Attempt.fail("Could not apply rule forallE on expression " + quantified.expression + ".") 
  }

  /** Reflexivity of equality.
   *
   * Contains the `Theorem`: `∀x. x = x`.
   */
  def reflexivity(tpe: Type): Attempt[Theorem] = {
    if (tpe == Untyped) {
      Attempt.typeError("reflexivity", tpe)
    }
    else {
      val x = Variable.fresh("x", tpe)

      Attempt.success(new Theorem(Forall(Seq(x.toVal), Equals(x, x))))
    }
  }

  def reflexivity(expr: Expr): Attempt[Theorem] = {
    if (expr.getType == Untyped) {
      Attempt.typeError("reflexivity", expr.getType)
    }
    else {
      Attempt.success(new Theorem(Equals(expr, expr)))
    }
  }

  def symmetry(tpe: Type): Attempt[Theorem] = {
    if (tpe == Untyped) {
      Attempt.typeError("reflexivity", tpe)
    }
    val a = Variable.fresh("a", tpe)
    val b = Variable.fresh("b", tpe)

    new Theorem(Forall(Seq(a.toVal, b.toVal), Implies(Equals(a, b), Equals(b, a))))
  }

  def symmetry(a: Expr, b: Expr): Attempt[Theorem] = {
    val tpeA = a.getType
    val tpeB = b.getType

    if (tpeA != tpeB || tpeA == Untyped) {
      Attempt.typeError("symmetry", TupleType(Seq(tpeA, tpeB)))
    }
    else {
      Attempt.success(new Theorem(Implies(Equals(a, b), Equals(b, a))))
    }
  }

  lazy val iffI: Theorem = {
    val a = Variable.fresh("a", BooleanType)
    val b = Variable.fresh("b", BooleanType)

    new Theorem(Equals(And(Implies(a, b), Implies(b, a)), Equals(a, b)))
  }

  lazy val iffE: Theorem = {
    val a = Variable.fresh("a", BooleanType)
    val b = Variable.fresh("b", BooleanType)

    new Theorem(Equals(Equals(a, b), And(Implies(a, b), Implies(b, a))))
  }

  def transitivity(a: Expr, b: Expr, c: Expr)
    (aEqualsB: Goal => Attempt[Witness], bEqualsC: Goal => Attempt[Witness]): Attempt[Theorem] = {

    val tpeA = a.getType
    val tpeB = b.getType
    val tpeC = c.getType

    if (tpeA != tpeB || tpeB != tpeC || tpeA == Untyped) {
      Attempt.typeError("transitivity", TupleType(Seq(tpeA, tpeB, tpeC)))
    }

    val goalAEqualsB = new Goal(Equals(a, b))
    val goalBEqualsC = new Goal(Equals(b, c))

    aEqualsB(goalAEqualsB) flatMap { (wAB: Witness) =>
      if (!goalAEqualsB.accepts(wAB)) {
        Attempt.incorrectWitness
      }
      else {
        bEqualsC(goalBEqualsC) flatMap { (wBC: Witness) =>
          if (!goalBEqualsC.accepts(wBC)) {
            Attempt.incorrectWitness
          }
          else {
            Attempt.success(new Theorem(Equals(a, c)).from(Seq(wAB.theorem, wBC.theorem)))
          }
        }
      }
    }

  }

  /** Truth.
   *
   * Contains the `Theorem` : `true`.
   */
  lazy val truth: Theorem = new Theorem(BooleanLiteral(true))

  lazy val excludedMiddle: Theorem = {
    val x = Variable.fresh("x", BooleanType)

    new Theorem(Forall(Seq(x.toVal), Or(x, Not(x))))
  }

  def excludedMiddle(expr: Expr): Attempt[Theorem] = {
    if (expr.getType == BooleanType) {
      Attempt.success(new Theorem(Or(expr, Not(expr))))
    }
    else {
      Attempt.typeError("excludedMiddle", expr.getType)
    }
  }

  /** Congruence of equality.
   *
   * Given a proven equality between two expressions and a context,
   * obtain a proven equality of the two expressions within the context.
   *
   * @param equality A proven equality between two expressions.
   * @param context  A context in which to embed the two expressions.
   * @return The equality of both expressions within context, or `None`.
   */
  def congruence(equality: Theorem)(context: Expr => Expr): Attempt[Theorem] = 
    equality.expression match {
      case Equals(a, b) => {
        // This should be the case since theorems can only hold boolean expressions.
        require(a.getType == b.getType && a.getType != Untyped)

        val f = freeze(a.getType, context)
        val inContextA = f(a)
        val inContextB = f(b)
        if (inContextA.getType != Untyped && inContextB != Untyped) {
          require(inContextA.getType == inContextB.getType)

          Attempt.success(new Theorem(Equals(inContextA, inContextB)).from(equality))       
        }
        else {
          Attempt.fail("Can not type expressions within context.")
        }
      }
      case _ => Attempt.fail("Can not apply congruence, expected equality, received " + equality.expression + ".")
    }

  def congruence(statement: Theorem, path: Path, replacement: Expr)
      (equalityProof: Goal => Attempt[Witness]): Attempt[Theorem] = {

    if (replacement.getType == Untyped) {
      return Attempt.typeError("congruence", replacement.getType)
    }

    val expr = statement.expression
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

    if (replacement.getType != original.getType) {
      // Replacement and original do not have the same type.
      return Attempt.typeError("congruence", replacement.getType)
    }

    val goal = new Goal(Equals(original, replacement))

    equalityProof(goal) flatMap { (witness: Witness) =>
      if (goal.accepts(witness)) {
        Attempt.success(new Theorem(focus.set(replacement)).from(Seq(statement, witness.theorem)))
      }
      else {
        Attempt.incorrectWitness
      }
    }
  }
}