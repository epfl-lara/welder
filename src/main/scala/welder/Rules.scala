/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.ast._

/** Contains introduction and elimination rules for many constructions. */
trait Rules { self: Theory =>
  import program.trees._

  /** Negation introduction.
   *
   * Proves the negation of some `hypothesis` by showing that it implies `false`.
   *
   * @param hypothesis    The hypothesis to disprove.
   * @param contradiction Proof of `false`, given the `hypothesis`.
   * @return A theorem for the negation of the hypothesis.
   */
  def notI(hypothesis: Expr)
          (contradiction: (Theorem, Goal) => Attempt[Witness]): Attempt[Theorem] = {

    val (hyp, mark) = new Theorem(hypothesis).mark
    val goal = new Goal(BooleanLiteral(false))

    catchFailedAttempts {
      for {
        witness <- contradiction(hyp, goal)
        theorem <- witness.extractTheorem(goal)
      } yield new Theorem(Not(hypothesis)).from(theorem).unmark(mark)
    }
  }

  // NOTE
  // 
  // This combinator can be derived from others.
  // No need for it to be primitive.
  //  
  // def notI2(hypothesis: Expr)
  //         (contradiction: (Theorem, Goal) => Attempt[Witness]): Attempt[Theorem] = {
  
  //   catchFailedAttempts {
  //     notI.forallE(hypothesis).implE(_.by(implI(hypothesis) { (hyp: Theorem) =>
  //       val goal = new Goal(BooleanLiteral(false))
  //       for {
  //         witness <- contradiction(hyp, goal)
  //         theorem <- witness.extractTheorem(goal)
  //       } yield theorem
  //     }))
  //   }
  // }


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
      catchFailedAttempts {
        cases(goal) flatMap { (witness: Witness) => witness.extractTheorem(goal) }
      }
    }

    Attempt.atLeastOne(attempts) map { (successfulTheorems: Seq[Theorem]) =>
      new Theorem(Or(expressions)).from(successfulTheorems)
    }
  } 

  /** Proves the disjunction of a sequence of expressions by proving at least one of the cases.
   *
   * @param first The first disjunct.
   * @param rest  The rest of the disjuncts.
   * @param cases Proof function, applied to each disjunct separately.
   * @return A `Theorem` for the disjunction.
   */
  def orI(first: Expr, rest: Expr*)(cases: Goal => Attempt[Witness]): Attempt[Theorem] =
    orI(first +: rest)(cases)

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

          catchFailedAttempts {
            cases(hyp, goal) flatMap { (witness: Witness) => witness.extractTheorem(goal).map(_.unmark(mark)) }
          }
        }

        Attempt.all(attempts) map { (theorems: Seq[Theorem]) =>
          new Theorem(conclusion).from(theorems)
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
   * @return A `Theorem` of the implication.
   */
  def implI(assumption: Expr)(conclusion: Theorem => Attempt[Theorem]): Attempt[Theorem] = {
    
    if (assumption.getType != BooleanType) {
      return Attempt.fail("Passed non-boolean expression " + assumption + " to implI.")
    }

    val (hypothesis, mark) = new Theorem(assumption).mark

    catchFailedAttempts {
      conclusion(hypothesis) map {
        (thm: Theorem) => new Theorem(Implies(assumption, thm.expression)).from(thm).unmark(mark)
      }
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

  /** Implication elimination.
   *
   * Given a proven `implication`, and a `proof` of the premise of the implication,
   * returns the conclusion as a `Theorem`.
   *
   * @param implication A proven implication. Should be of the form `Implies( ... )`.
   * @param proof       Proof of the premise of the implication.
   * @return The proven conclusion.
   */
  def implE(implication: Theorem)(proof: Goal => Attempt[Witness]): Attempt[Theorem] = 
    implication.expression match {
      case Implies(condition, body) => {
        val goal = new Goal(condition)

        catchFailedAttempts {
          for {
            witness <- proof(goal)
            theorem <- witness.extractTheorem(goal)
          } yield new Theorem(body).from(theorem)
        }
      } 
      case _ => Attempt.fail("Could not apply rule implE on non-implication expression " + implication.expression + ".")
    }


  def forallI(vd: ValDef)(theorem: Variable => Attempt[Theorem]): Attempt[Theorem] = {
    catchFailedAttempts {
      theorem(vd.toVariable) map { (thm: Theorem) =>
        new Theorem(Forall(Seq(vd), thm.expression)).from(thm)
      }
    }
  }

  def forallI(vd1: ValDef, vd2: ValDef)
             (theorem: (Variable, Variable) => Attempt[Theorem]): Attempt[Theorem] = {
    catchFailedAttempts {
      theorem(vd1.toVariable, vd2.toVariable) map { (thm: Theorem) =>
        new Theorem(Forall(Seq(vd1, vd2), thm.expression)).from(thm)
      }
    }
  }

  def forallI(vd1: ValDef, vd2: ValDef, vd3: ValDef)
             (theorem: (Variable, Variable, Variable) => Attempt[Theorem]): Attempt[Theorem] = {
    catchFailedAttempts {
      theorem(vd1.toVariable, vd2.toVariable, vd3.toVariable) map { (thm: Theorem) =>
        new Theorem(Forall(Seq(vd1, vd2, vd3), thm.expression)).from(thm)
      }
    }
  }

  def forallI(vd1: ValDef, vd2: ValDef, vd3: ValDef, vd4: ValDef)
             (theorem: (Variable, Variable, Variable, Variable) => Attempt[Theorem]): Attempt[Theorem] = {
    catchFailedAttempts {
      theorem(vd1.toVariable, vd2.toVariable, vd3.toVariable, vd4.toVariable) map { (thm: Theorem) =>
        new Theorem(Forall(Seq(vd1, vd2, vd3, vd4), thm.expression)).from(thm)
      }
    }
  }

  def forallI(vds: Seq[ValDef])(theorem: Seq[Variable] => Attempt[Theorem]): Attempt[Theorem] = {
    catchFailedAttempts {
      theorem(vds.map(_.toVariable)) map { (thm: Theorem) =>
        new Theorem(Forall(vds, thm.expression)).from(thm)
      }
    }
  }

  def forallE(quantified: Theorem)(first: Expr, rest: Expr*): Attempt[Theorem] = forallE(quantified, first +: rest)

  def forallE(quantified: Theorem, terms: Seq[Expr]): Attempt[Theorem] = quantified.expression match {
    // TODO: Be less strict here. What if less arguments are given than quantified variables?
    //       What if more are given and `expression` is also a Forall-quantified expression?

    case Forall(defs, expression) if terms.size == defs.size => {

      val substitutions = defs.zip(terms).toMap

      val typeError = substitutions.exists { case (vd, e) =>
        !symbols.isSubtypeOf(e.getType, vd.getType)
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

  def existsI(expr: Expr, name: String)(theorem: Theorem): Attempt[Theorem] = {
    existsI(root ~~ is(expr), name)(theorem)
  }

  def existsI(path: Path, name: String)(theorem: Theorem): Attempt[Theorem] = {
    val focuses = path.on(theorem.expression)

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

    val tpe = original.getType
    val valDef = ValDef(FreshIdentifier(name), tpe)

    val replaced = focus.set(valDef.toVariable)

    Attempt.success {
      new Theorem(replaced match {
        case Not(Forall(vds, body)) => Not(Forall(valDef +: vds, body))
        case _ => Not(Forall(Seq(valDef), Not(replaced)))
      }).from(theorem)
    }
  }

  def existsE(quantified: Theorem): Attempt[(Variable, Theorem)] = quantified.expression match {
    case Not(Forall(Seq(vd), Not(body))) => {
      val variable = vd.freshen.toVariable
      val substitutions = Map(vd -> variable)
      Attempt.success((variable), new Theorem(exprOps.replaceFromSymbols(substitutions, body)).from(quantified))
    }
    case Not(Forall(Seq(vd), body)) => {
      val variable = vd.freshen.toVariable
      val substitutions = Map(vd -> variable)
      Attempt.success((variable), new Theorem(Not(exprOps.replaceFromSymbols(substitutions, body))).from(quantified))
    }
    case Not(Forall(vds, body)) => {
      val vd = vds.head
      val variable = vd.freshen.toVariable
      val substitutions = Map(vd -> variable)
      Attempt.success((variable), new Theorem(Not(Forall(vds.tail, exprOps.replaceFromSymbols(substitutions, body)))).from(quantified))
    }
    case _ => Attempt.fail("Could not apply rule existsE.")
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

  def transitivity(tpe: Type): Attempt[Theorem] = {
    if (tpe == Untyped) {
      Attempt.typeError("transitivity", tpe)
    }
    else {
      val a = Variable.fresh("a", tpe)
      val b = Variable.fresh("b", tpe)
      val c = Variable.fresh("c", tpe)

      Attempt.success(new Theorem(Forall(Seq(a, b, c).map(_.toVal),
        Implies(And(Equals(a, b), Equals(b, c)), Equals(a, c)))))
    }
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

    val attemptAB = catchFailedAttempts { 
        for {
        wAB <- aEqualsB(goalAEqualsB)
        tAB <- wAB.extractTheorem(goalAEqualsB)
      } yield tAB
    }

    val attemptBC = catchFailedAttempts {
      for {
        wBC <- bEqualsC(goalBEqualsC)
        tBC <- wBC.extractTheorem(goalBEqualsC)
      } yield tBC
    }

    Attempt.all(Seq(attemptAB, attemptBC)) map { case Seq(tAB, tBC) =>
      new Theorem(Equals(a, c)).from(Seq(tAB, tBC))
    }
  }

  /** Truth.
   *
   * Contains the `Theorem` : `true`.
   */
  lazy val truth: Theorem = new Theorem(BooleanLiteral(true))

  // TODO: Should we get rid of this ? Seems a bit like a hack.

  /** Falsitude.
   *
   * Contains the `Theorem` : `false`. The theorem, or any theorem
   * derived from it, will never be globally valid.
   *
   * Could be used while developing proofs to momentarily assume anything.
   */
  lazy val absurd: Theorem = {

    // We purposely ignore the mark. The Theorem will never be globally valid. 
    val (thm, _) = new Theorem(BooleanLiteral(false)).mark

    thm
  }

  /** Excluded middle.
   *
   * Contains the `Theorem`: `∀x: Boolean. x ∨ ¬x`.
   */
  lazy val excludedMiddle: Theorem = {
    val x = Variable.fresh("x", BooleanType)

    new Theorem(Forall(Seq(x.toVal), Or(x, Not(x))))
  }

  /** Excluded middle.
   *
   * States that the expression `expr` of type `Boolean`
   * is either `true` or `false`.
   */
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
   * @return The equality of both expressions within context.
   */
  def congruence(equality: Theorem)(context: Expr => Expr): Attempt[Theorem] = 
    equality.expression match {
      case Equals(a, b) => {
        // This should be the case since theorems can only hold
        // well-typed boolean expressions.
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

  /** Congruence.
   *
   * Replaces, within a proven `statement`, the expression pointed by `path`
   * by the `replacement`, given that a proof that the two expressions are equal.
   *
   * @param statement     A proven statement.
   * @param path          A path describing which part of the statement to modify.
   * @param replacement   The expression to plug into the statement.
   * @param equalityProof Proof that both expressions are equal.
   * @return The statement with the replacement expressions plugged in.
   */
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

    catchFailedAttempts {
      for {
        witness <- equalityProof(goal)
        theorem <- witness.extractTheorem(goal)
      } yield new Theorem(focus.set(replacement)).from(Seq(statement, theorem))
    }
  }
}