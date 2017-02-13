package welder

import scala.language.implicitConversions

trait Equational { self: Theory =>

  import program.trees._

  trait AcceptsProof {
    def ==|(t: Theorem): Node
  }

  trait Node {
    def |==(node: Node): Chain = {
      val thiz = this

      new Chain {
        val first = thiz.first
        val next = node.next
        val last = node.first
        def equality = prove(Equals(thiz.first, node.first), thiz.next)
      }
    }
    def |==(end: Expr): Attempt[Theorem] =
      prove(Equals(this.first, end), this.next)

    val first: Expr
    val next: Theorem
  }

  trait Chain extends Node {
    val last: Expr
    def equality: Attempt[Theorem]

    override def |==(node: Node): Chain = {
      val thiz = this

      new Chain {
        val first = thiz.first
        val last = node.first
        val equality = transitivity(thiz.first, thiz.last, node.first)(
          { (goal: Goal) => thiz.equality.flatMap(goal.by(_)) },
          { (goal: Goal) => goal.by(thiz.next) })
        val next = node.next
      }
    }
    override def |==(end: Expr): Attempt[Theorem] = transitivity(this.first, this.last, end)(
      { (goal: Goal) => this.equality.flatMap(goal.by(_)) },
      { (goal: Goal) => goal.by(this.next) })
  }

  implicit def exprToAcceptsProof(expr: Expr): AcceptsProof = new AcceptsProof {
    def ==|(t: Theorem): Node = new Node {
      val first = expr
      val next = t
    }
  }
}