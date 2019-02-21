/* Copyright 2017 EPFL, Lausanne */

package welder

import inox.Identifier

trait Deconstructions { self: Theory =>
  
  import program.trees._

  sealed trait FinitelyDeconstructable[T <: Type] {
    type Expression <: Expr
    type Constructor

    def cases(tpe: T): Seq[(Constructor, Expression, Seq[Variable])]
  }

  // implicit object BooleanDeconstructable extends FinitelyDeconstructable[BooleanType.type] {
  //   type Expression = BooleanLiteral

  //   def cases(tpe: BooleanType.type): Seq[(Expression, Seq[Variable])] =
  //     Seq((BooleanLiteral(false), Seq()), (BooleanLiteral(true), Seq()))
  // }

  // implicit object UnitDeconstructable extends FinitelyDeconstructable[UnitType.type] {
  //   type Expression = UnitLiteral

  //   def cases(tpe: UnitType.type): Seq[(Expression, Seq[Variable])] =
  //     Seq((UnitLiteral(), Seq()))
  // }

  // implicit object BVDeconstructable extends FinitelyDeconstructable[BVType] {
  //   type Expression = Tuple

  //   def cases(tpe: BVType): Seq[(Expression, Seq[Variable])] = Seq {
  //     val variables = Seq.tabulate(tpe.size) { (n: Int) =>
  //       val name = "bit_" + n.toString
  //       Variable.fresh(name, BooleanType)
  //     }

  //     val expr = Tuple(variables)

  //     (expr, variables)
  //   }
  // }

  implicit object ADTDeconstructable extends FinitelyDeconstructable[ADTType] {
    type Expression = ADT
    type Constructor = Identifier

    def cases(tpe: ADTType): Seq[(Constructor, Expression, Seq[Variable])] = {

      val constructors = tpe.getSort.constructors

      constructors map { constructor: TypedADTConstructor =>
        val variables = constructor.fields map { (field: ValDef) =>
          val name = field.toVariable.id.name
          Variable.fresh(name, field.tpe)
        }

        val expr = ADT(constructor.id, constructor.tps, variables)

        (constructor.definition.id, expr, variables)
      }
    }
  }

  implicit object TupleDeconstructable extends FinitelyDeconstructable[TupleType] {

    type Expression = Tuple
    type Constructor = Unit

    def cases(tpe: TupleType): Seq[(Constructor, Expression, Seq[Variable])] = Seq {
      val variables = tpe.bases.zipWithIndex map { case (inner: Type, index: Int) =>
        val name = "t_" + index.toString
        Variable.fresh(name, inner)
      }

      val expr = Tuple(variables)

      ((), expr, variables)
    }
  }
}