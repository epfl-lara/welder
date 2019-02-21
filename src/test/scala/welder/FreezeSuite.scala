
package welder

import inox._
import inox.evaluators._
import inox.trees._

import org.scalatest._

class FreezeSuite extends FunSuite {
  
  object Empty extends Theory {
    override val program: InoxProgram = Program(inox.trees)(NoSymbols)
    override val ctx: Context = Context.empty
  }

  import Empty._

  def assertSameResult(f: Expr => Expr, g: Expr => Expr)(x: Expr) {
    assert(f(x) == g(x))
  }

  test("Freeze works on constant functions") {

    def original(x: Expr) = BooleanLiteral(false)

    val frozen = freeze(IntegerType(), original)

    val assertSameOn = assertSameResult(original, frozen) _

    assertSameOn(IntegerLiteral(12))
    assertSameOn(Variable.fresh("x", IntegerType()))
    assertSameOn(Plus(IntegerLiteral(17), IntegerLiteral(-5)))
    assertSameOn(Division(IntegerLiteral(1), Variable.fresh("y", IntegerType())))
  }

  test("Freeze works on well-behaved functions") {

    def original(x: Expr) = Times(Plus(x, IntegerLiteral(5)), IntegerLiteral(2))

    val frozen = freeze(IntegerType(), original)

    val assertSameOn = assertSameResult(original, frozen) _

    assertSameOn(IntegerLiteral(12))
    assertSameOn(Variable.fresh("x", IntegerType()))
    assertSameOn(Plus(IntegerLiteral(17), IntegerLiteral(-5)))
    assertSameOn(Division(IntegerLiteral(1), Variable.fresh("y", IntegerType())))
  }

  test("Freeze works on ill-behaved functions (procedures)") {

    var i: BigInt = 0

    def original(x: Expr) = {
      i += 1
      IntegerLiteral(i)
    }

    // Checks that the function is indeed ill-behaved.
    assert(original(IntegerLiteral(1)) != original(IntegerLiteral(1)))

    val frozen = freeze(IntegerType(), original)

    // Checks that frozen returns the same result in each invocation.
    val assertSameOn = assertSameResult(frozen, frozen) _

    assertSameOn(IntegerLiteral(12))
    assertSameOn(Variable.fresh("x", IntegerType()))
    assertSameOn(Plus(IntegerLiteral(17), IntegerLiteral(-5)))
    assertSameOn(Division(IntegerLiteral(1), Variable.fresh("y", IntegerType())))
  }

  test("Freeze works on ill-behaved functions (functions inspecting their argument)") {

    def original(x: Expr) = x match {
      case Plus(a, b)  => a
      case Times(a, b) => b
      case _ => Times(x, IntegerLiteral(7))
    }

    val evaluator: DeterministicEvaluator { val program: InoxProgram } = {
      RecursiveEvaluator(Empty.program, Empty.ctx)
    }

    // Checks that the function is indeed ill-behaved.
    assert(evaluator.eval(original(Plus(IntegerLiteral(1), IntegerLiteral(1)))) != 
      evaluator.eval(original(IntegerLiteral(2))))

    val frozen = freeze(IntegerType(), original)

    // Checks that the frozen function is indeed well-behaved.
    assert(evaluator.eval(frozen(Plus(IntegerLiteral(1), IntegerLiteral(1)))) == 
      evaluator.eval(frozen(IntegerLiteral(2))))

    // Checks that frozen returns the same result in each invocation.
    val assertSameOn = assertSameResult(frozen, frozen) _

    assertSameOn(IntegerLiteral(12))
    assertSameOn(Variable.fresh("x", IntegerType()))
    assertSameOn(Plus(IntegerLiteral(17), IntegerLiteral(-5)))
    assertSameOn(Division(IntegerLiteral(1), Variable.fresh("y", IntegerType())))
  }
}