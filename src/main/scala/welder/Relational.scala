/* Copyright 2017 EPFL, Lausanne */

package welder

import scala.language.implicitConversions

import inox.InoxProgram

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
trait Relational { self: Theory =>

  import program.trees._

  object relations { 

    sealed abstract class Rel {
      def apply(lhs: Expr, rhs: Expr): Expr = this match {
        case LE => LessEquals(lhs, rhs)
        case LT => LessThan(lhs, rhs)
        case EQ => Equals(lhs, rhs)
        case GT => GreaterThan(lhs, rhs)
        case GE => GreaterEquals(lhs, rhs)
      }
    }
    case object LE extends Rel
    case object LT extends Rel
    case object EQ extends Rel
    case object GT extends Rel
    case object GE extends Rel

    def compose(rel1: Rel, rel2: Rel): Option[Rel] = (rel1, rel2) match {
      case (EQ, b) => Some(b)
      case (a, EQ) => Some(a)
      case (LT, LT | LE) => Some(LT)
      case (LE, LT) => Some(LT)
      case (LE, LE) => Some(LE)
      case (GT, GT | GE) => Some(GT)
      case (GE, GT) => Some(GT)
      case (GE, GE) => Some(GE)
      case _ => None
    }
  }
  import relations._

  /** Denotes that a proof is expected next. */
  implicit class WithRelations(expr: Expr) {

    /** Adds a theorem as justification for the next equality. */
    def ==|(theorem: Theorem): EqChain =
      new EqChain(toNode(EQ, theorem))

    /** Adds a proof as justification for the next equality. */
    def ==|(proof: Goal => Attempt[Witness]): EqChain =
      new EqChain(toNode(EQ, proof))

    /** Adds a theorem as justification for the next relation. */
    def >=|(theorem: Theorem): GreaterEqChain =
      new GreaterEqChain(toNode(GE, theorem))

    /** Adds a proof as justification for the next relation. */
    def >=|(proof: Goal => Attempt[Witness]): GreaterEqChain =
      new GreaterEqChain(toNode(GE, proof))

    /** Adds a theorem as justification for the next relation. */
    def >>|(theorem: Theorem): GreaterChain =
      new GreaterChain(toNode(GT, theorem))

    /** Adds a proof as justification for the next relation. */
    def >>|(proof: Goal => Attempt[Witness]): GreaterChain =
      new GreaterChain(toNode(GT, proof))

    /** Adds a theorem as justification for the next relation. */
    def <=|(theorem: Theorem): LessEqChain =
      new LessEqChain(toNode(LE, theorem))

    /** Adds a proof as justification for the next relation. */
    def <=|(proof: Goal => Attempt[Witness]): LessEqChain =
      new LessEqChain(toNode(LE, proof))

    /** Adds a theorem as justification for the next relation. */
    def <<|(theorem: Theorem): LessChain =
      new LessChain(toNode(LT, theorem))

    /** Adds a proof as justification for the next relation. */
    def <<|(proof: Goal => Attempt[Witness]): LessChain =
      new LessChain(toNode(LT, proof))

    private def toNode(relation: Rel, theorem: Theorem): Node = toNode(relation, _.by(theorem))

    private def toNode(relation: Rel, proof: Goal => Attempt[Witness]): Node = new Node {
      val first = expr
      val nextRel = relation
      val next = proof
    }
  }

  trait HasNode {
    val node: Node

    def |(end: Expr): Attempt[Theorem] = node.append(end)
  }

  class EqChain(val node: Node) extends HasNode {
    def |(chain: LessChain): LessChain = new LessChain(node.append(chain.node))
    def |(chain: LessEqChain): LessEqChain = new LessEqChain(node.append(chain.node))
    def |(chain: EqChain): EqChain = new EqChain(node.append(chain.node))
    def |(chain: GreaterChain): GreaterChain = new GreaterChain(node.append(chain.node))
    def |(chain: GreaterEqChain): GreaterEqChain = new GreaterEqChain(node.append(chain.node))
  }

  class LessChain(val node: Node) extends HasNode {
    def |(chain: LessChain): LessChain = new LessChain(node.append(chain.node))
    def |(chain: LessEqChain): LessChain = new LessChain(node.append(chain.node))
    def |(chain: EqChain): LessChain = new LessChain(node.append(chain.node))
  }

  class LessEqChain(val node: Node) extends HasNode {
    def |(chain: LessChain): LessChain = new LessChain(node.append(chain.node))
    def |(chain: LessEqChain): LessEqChain = new LessEqChain(node.append(chain.node))
    def |(chain: EqChain): LessEqChain = new LessEqChain(node.append(chain.node)) 
  }

  class GreaterChain(val node: Node) extends HasNode {
    def |(chain: GreaterChain): GreaterChain = new GreaterChain(node.append(chain.node))
    def |(chain: GreaterEqChain): GreaterChain = new GreaterChain(node.append(chain.node))
    def |(chain: EqChain): GreaterChain = new GreaterChain(node.append(chain.node))
  }

  class GreaterEqChain(val node: Node) extends HasNode {
    def |(chain: GreaterChain): GreaterChain = new GreaterChain(node.append(chain.node))
    def |(chain: GreaterEqChain): GreaterEqChain = new GreaterEqChain(node.append(chain.node))
    def |(chain: EqChain): GreaterEqChain = new GreaterEqChain(node.append(chain.node))
  }

  trait Node {

    private[welder] val nextRel: Rel

    /** First expression. */
    private[welder] val first: Expr

    /** Justification for the next step. */
    private[welder] val next: Goal => Attempt[Witness]

    /** Sets the next expression, and following justification, in the chain. */
    private[welder] def append(node: Node): Chain = {
      val thiz = this

      new Chain {
        val rel = thiz.nextRel
        val nextRel = node.nextRel
        val first = thiz.first
        val next = node.next
        val last = node.first
        def relation = {
          val goal = new Goal(thiz.nextRel(thiz.first, node.first))

          catchFailedAttempts {
            for {
              witness <- thiz.next(goal)
              theorem <- witness.extractTheorem(goal)
            } yield theorem
          }
        }
      }
    }

    /** Sets the last expression in the equality chain. */
    private[welder] def append(end: Expr): Attempt[Theorem] = {

      val goal = new Goal(nextRel(first, end))
      catchFailedAttempts {
        for {
          witness <- next(goal)
          theorem <- witness.extractTheorem(goal)
        } yield theorem
      }
    }
  }

  /** Chain of equalities, with proof for the following equality. */
  trait Chain extends Node {

    /** Last seen expression. */
    private[welder] val last: Expr

    private[welder] val rel: Rel

    /** Theorem stating the relation between the `first` and `last` expressions. */
    private[welder] def relation: Attempt[Theorem]

    /** Sets the next expression, and following justification, in the equality chain. */
    override private[welder] def append(node: Node): Chain = {
      val thiz = this

      val newRel = compose(this.rel, this.nextRel).get  // Should never fail thanks to types.

      new Chain {
        val rel = newRel
        val nextRel = node.nextRel
        val first = thiz.first
        val last = node.first
        val relation = {
          val goal = new Goal(thiz.nextRel(thiz.last, node.first))
          val attemptNext = for {
            witness <- thiz.next(goal)
            theorem <- witness.extractTheorem(goal)
          } yield theorem

          Attempt.all(Seq(thiz.relation, attemptNext)) flatMap {
            case Seq(thmRel, thmNext) => prove(newRel(thiz.first, node.first), thmRel, thmNext)
          }
        }
        val next = node.next
      }
    }

    /** Sets the last expression in the equality chain. */
    override private[welder] def append(end: Expr): Attempt[Theorem] = {
      val newRel = compose(rel, nextRel).get  // Should never fail thanks to types.

      val goal = new Goal(nextRel(last, end))
      val attemptNext = for {
        witness <- next(goal)
        theorem <- witness.extractTheorem(goal)
      } yield theorem

      Attempt.all(Seq(relation, attemptNext)) flatMap {
        case Seq(thmRel, thmNext) => prove(newRel(first, end), thmRel, thmNext)
      }
    }
  }
}