/* Copyright 2017 EPFL, Lausanne */

package welder

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.interpolator._

import org.scalatest._

class UnsoundConstructsSuite extends FunSuite {

  val list: Identifier = FreshIdentifier("List")
  val cons: Identifier = FreshIdentifier("Cons")
  val nil: Identifier = FreshIdentifier("Nil")
  val head: Identifier = FreshIdentifier("head")
  val tail: Identifier = FreshIdentifier("tail")
  val length: Identifier = FreshIdentifier("length")

  val invariant: Identifier = FreshIdentifier("invariant")
  val invariantFunction = mkFunDef(invariant)("A") { case Seq(a) =>
    val args: Seq[ValDef] = Seq("xs" :: T(list)(a))
    val retType: Type = BooleanType
    val body: Seq[Variable] => Expr = { case Seq(xs) =>
      if_ (xs.isInstOf(T(cons)(a))) {
        let ("c" :: T(cons)(a), xs.asInstOf(T(cons)(a))) { case c =>
          if_ (c.getField(tail).isInstOf(T(cons)(a))) {
            c.getField(length) === (c.getField(tail).asInstOf(T(cons)(a)).getField(length) + E(BigInt(1)))
          } else_ {
            c.getField(length) === E(BigInt(1))
          }
        }
      } else_ {
        E(true)
      }
    }

    (args, retType, body)
  }

  val listSort = mkSort(list, HasADTInvariant(invariant))("A")(Seq(cons, nil))
  val consConstructor = mkConstructor(cons)("A")(Some(list)) {
    case Seq(a) =>
      Seq(ValDef(head, a), ValDef(length, IntegerType), ValDef(tail, T(list)(a)))
  }
  val nilConstructor = mkConstructor(nil)("A")(Some(list))(tps => Seq.empty)

  val symbols = NoSymbols.withFunctions(Seq(invariantFunction)).withADTs(Seq(listSort, consConstructor, nilConstructor))
  val program = InoxProgram(Context.empty, symbols)

  val theory = welder.theoryOf(program)
  import theory._

  def assertSuccessful(attempt: => Attempt[_]) {
    assert(attempt.isSuccessful)
  }

  def assertFailure(attempt: => Attempt[_]) {
    assert(!attempt.isSuccessful)
  }

  test("Correct ADT invariant.") {
    implicit val sb = symbols
    assertSuccessful(prove(e"Cons(0, 1, Nil()).head == 0"))
    assertSuccessful(prove(e"Cons(1.5, 1, Nil()).head == 1.5"))
    assertSuccessful(prove(e"Cons(42, 2, Cons(17, 1, Nil())).head == 42"))
    assertSuccessful(prove(e"Cons('foo', 1, Nil()).head == 'foo'"))
    assertSuccessful(prove(e"Nil[BigInt]() == Nil()"))
  }

  test("Incorrect ADT invariant.") {
    implicit val sb = symbols
    assertFailure(prove(e"Cons(0, 2, Nil()).head == 0"))
    assertFailure(prove(e"Cons(42, 3, Cons(17, 1, Nil())).head == 42"))
    assertFailure(prove(e"Cons(42, 3, Cons(17, 2, Nil())).head == 42"))
  }

}