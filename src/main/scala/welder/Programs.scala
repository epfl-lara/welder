/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.trees._
import inox.trees.dsl._

object NoProgram extends Theory {
  override val program = InoxProgram(Context.empty, NoSymbols)
}

object ListProgram extends Theory {

  val list: Identifier = FreshIdentifier("List")
  val cons: Identifier = FreshIdentifier("Cons")
  val nil: Identifier = FreshIdentifier("Nil")
  val head: Identifier = FreshIdentifier("head")
  val tail: Identifier = FreshIdentifier("tail")

  val listSort = mkSort(list)("A")(Seq(cons, nil))
  val consConstructor = mkConstructor(cons)("A")(Some(list)) {
    case Seq(tp) =>
      Seq(ValDef(head, tp), ValDef(tail, T(list)(tp)))
  }
  val nilConstructor = mkConstructor(nil)("A")(Some(list))(tps => Seq.empty)

  override val program = InoxProgram(Context.empty, NoSymbols.withADTs(Seq(listSort, consConstructor, nilConstructor)))
}

object SumProgram extends Theory {

  val sum: Identifier = FreshIdentifier("sum")

  val sumFunction = mkFunDef(sum)() { case _ =>
    val args: Seq[ValDef] = Seq("n" :: IntegerType)
    val retType: Type = IntegerType
    val body: Seq[Variable] => Expr = { case Seq(n) =>
      if_ (Equals(n, IntegerLiteral(0))) {
        IntegerLiteral(0)
      } else_ {
        Plus(FunctionInvocation(sum, Seq(), Seq(Minus(n, IntegerLiteral(1)))), n)
      }
    }

    (args, retType, body)
  }

  override val program = InoxProgram(Context.empty, NoSymbols.withFunctions(Seq(sumFunction)))


  lazy val proofGauss: Theorem = {
    def property(x: Expr) = Equals(
      FunctionInvocation(sum, Seq(), Seq(x)),
      Division(Times(x, Plus(x, IntegerLiteral(1))), IntegerLiteral(2)))

    // Would be nice to have: e"sum($x) == ($x * ($x + 1)) / 2"

    naturalInduction(property, IntegerLiteral(0), _.trivial) { case (ihs, goal) =>

      val lemma = Equals(
        FunctionInvocation(sum, Seq(), Seq(Plus(ihs.variable, IntegerLiteral(1)))),
        Plus(FunctionInvocation(sum, Seq(), Seq(ihs.variable)), Plus(ihs.variable, IntegerLiteral(1))))

      val provenLemma: Theorem = prove(lemma, ihs.variableGreaterThanBase)

      goal.by(andI(provenLemma, ihs.propertyForVar))
    }
  }
}