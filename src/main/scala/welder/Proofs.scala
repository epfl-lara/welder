/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.trees._

trait Proofs { self: Theory =>

  type MetaIdentifier = String

  sealed abstract class Proof
  case class Variable(id: MetaIdentifier) extends Proof
  case class Axiom(theorem: Theorem) extends Proof
  case class ImplI(id: MetaIdentifier, hypothesis: Expr, conclusion: Proof) extends Proof
  case class ImplE(implication: Proof, hypothesis: Proof) extends Proof
  case class ForallI(vd: ValDef, body: Proof) extends Proof
  case class ForallE(quantified: Proof, value: Expr) extends Proof
  case class AndI(proofs: Seq[Proof]) extends Proof
  case class AndE(conjunction: Proof, parts: Seq[MetaIdentifier], body: Proof) extends Proof
  case class OrI(alternatives: Seq[Expr], theorem: Proof) extends Proof
  case class OrE(disjunction: Proof, conclusion: Expr, id: MetaIdentifier, cases: Seq[Proof]) extends Proof
  // case class NaturalInduction(expr: Expr, base: Expr, id: MetaIdentifier, baseCase: Proof, inductiveCase: Proof) extends Proof
  case class Prove(expr: Expr, hypotheses: Seq[Proof]) extends Proof
  case class Let(named: Proof, id: MetaIdentifier, body: Proof) extends Proof

  def interpret(proof: Proof): Attempt[Theorem] = {
    def go(proof: Proof, bindings: Map[MetaIdentifier, Theorem]): Attempt[Theorem] = proof match {
      case Variable(id) => bindings.get(id).map(Attempt.success(_)).getOrElse(Attempt.fail("No such meta variable: " + id))
      case Axiom(theorem) => theorem
      case ImplI(id, hypothesis, conclusion) => implI(hypothesis) { theorem =>
        go(conclusion, bindings + (id -> theorem))
      }
      case ImplE(implication, hypothesis) => for {
        i <- go(implication, bindings)
        h <- go(hypothesis, bindings)
        t <- implE(i) { goal =>
          goal.by(h)
        }
      } yield t
      case ForallI(vd, body) => {
        forallI(vd) { case _ => go(body, bindings) }  // TODO: Rename vd.toVar into var when/if forallI freshens the variable.
      }
      case ForallE(quantified, value) => for {
        q <- go(quantified, bindings)
        t <- forallE(q)(value)
      } yield t
      case AndI(proofs) => for {
        ts <- Attempt.all(proofs.map(go(_, bindings)))
      } yield andI(ts)
      case AndE(conjunction, parts, body) => for {
        c  <- go(conjunction, bindings)
        ps <- andE(c)
        t  <- go(body, bindings ++ parts.zip(ps).toMap)
      } yield t
      case OrI(alternatives, theorem) => for {
        p <- go(theorem, bindings)
        t <- orI(alternatives) { goal => goal.by(p) }
      } yield t
      case OrE(disjunction, conclusion, id, cases) => for {
        d <- go(disjunction, bindings)
        t <- orE(d, conclusion, cases.map { case proof =>
          { (theorem: Theorem, goal: Goal) => go(proof, bindings + (id -> theorem)).flatMap(goal.by(_)) }
        })
      } yield t
      case Prove(expr, hypotheses) => for {
        hs <- Attempt.all(hypotheses.map(go(_, bindings)))
        t  <- prove(expr, hs)
      } yield t
      case Let(named, id, body) => for {
        n <- go(named, bindings)
        t <- go(body, bindings + (id -> n))
      } yield t
    }

    go(proof, Map())
  }
}