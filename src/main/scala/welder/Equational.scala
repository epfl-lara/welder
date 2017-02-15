package welder

import scala.language.implicitConversions

/** Provides an equational reasoning DSL. 
 *
 * Allows chains of equalities to be written in the following way:
 *
 * {{{
 * expression1 ==| proof1is2 |
 * expression2 ==| proof2is3 |
 * expression3
 * }}}
 */
trait Equational { self: Theory =>

  import program.trees._

  /** Denotes that a proof is expected next. */
  trait AcceptsProof {

    /** Adds a theorem as justification for the next equality. */
    def ==|(theorem: Theorem): Node

    /** Adds a proof as justification for the next equality. */
    def ==|(proof: Goal => Attempt[Witness]): Node
  }

  /** Denotes the first expression and the proof of the next equality. */
  trait Node {

    /** First expression. */
    private[welder] val first: Expr

    /** Justification for the next step. */
    private[welder] val next: Goal => Attempt[Witness]

    /** Sets the next expression, and following justification, in the equality chain. */
    def |(node: Node): Chain = {
      val thiz = this

      new Chain {
        val first = thiz.first
        val next = node.next
        val last = node.first
        def equality = {
          val goal = new Goal(Equals(thiz.first, node.first))
          thiz.next(goal) flatMap { (w: Witness) => 
            if (!goal.accepts(w)) {
              Attempt.incorrectWitness
            }
            else {
              Attempt.success(w.theorem)
            }
          }
        }
      }
    }

    /** Sets the last expression in the equality chain. */
    def |(end: Expr): Attempt[Theorem] = {

      val goal = new Goal(Equals(this.first, end))
      this.next(goal) flatMap { (w: Witness) => 
        if (!goal.accepts(w)) {
          Attempt.incorrectWitness
        }
        else {
          Attempt.success(w.theorem)
        }
      }
    }
  }

  /** Chain of equalities, with proof for the following equality. */
  trait Chain extends Node {

    /** Last seen expression. */
    private[welder] val last: Expr

    /** Theorem stating the equality of the `first` and `last` expressions. */
    private[welder] def equality: Attempt[Theorem]

    /** Sets the next expression, and following justification, in the equality chain. */
    override def |(node: Node): Chain = {
      val thiz = this

      new Chain {
        val first = thiz.first
        val last = node.first
        val equality = transitivity(thiz.first, thiz.last, node.first)(
          { (goal: Goal) => thiz.equality.flatMap(goal.by(_)) },
          { (goal: Goal) => thiz.next(goal) })
        val next = node.next
      }
    }

    /** Sets the last expression in the equality chain. */
    override def |(end: Expr): Attempt[Theorem] = transitivity(this.first, this.last, end)(
      { (goal: Goal) => this.equality.flatMap(goal.by(_)) },
      { (goal: Goal) => this.next(goal) })
  }

  /** Decorates an expression with methods to add a proof for the following step. */
  implicit def exprToAcceptsProof(expr: Expr): AcceptsProof = new AcceptsProof {
    
    /** Adds a theorem as justification for the next equality. */
    def ==|(theorem: Theorem): Node = new Node {
      val first = expr
      val next = (goal: Goal) => goal.by(theorem)
    }

    /** Adds a proof as justification for the next equality. */
    def ==|(proof: Goal => Attempt[Witness]): Node = new Node {
      val first = expr
      val next = proof
    }
  }
}