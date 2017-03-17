package welder
package parsing

/** Contains description of (type-checking) constraints and
 *  and constrained values.
 */
trait Constraints {

  val trees: inox.ast.Trees
  val symbols: trees.Symbols

  import trees.Type

  /** Represents a meta type-parameter. */
  case class Unknown(val param: BigInt) extends Type {
    override def toString: String = "MetaParam(" + param + ")"
  }

  object Unknown {
    def fresh: Unknown = Unknown(Unique.fresh)
  }

  object Unique {
    var i: BigInt = 0

    def fresh: BigInt = synchronized {
      val ret = i
      i += 1
      ret
    }
  }

  /** Maps meta type-parameters to actual types. */
  class Unifier(mappings: Map[Unknown, Type]) {

    val instantiator = new trees.SelfTreeTransformer {
      override def transform(tpe: Type) = tpe match {
        case u: Unknown if mappings.contains(u) => transform(mappings(u))  // TODO: Is the recursive call necessary ?
        case _ => super.transform(tpe)
      }
    }

    def apply(tpe: Type): Type = instantiator.transform(tpe)
    def apply(c: Constraint): Constraint = c match {
      case Equal(a, b) => Equal(instantiator.transform(a), instantiator.transform(b))
      case Subtype(a, b) => Subtype(instantiator.transform(a), instantiator.transform(b))
      case IsNumeric(a) => IsNumeric(instantiator.transform(a))
      case IsComparable(a) => IsComparable(instantiator.transform(a))
      case IsIntegral(a) => IsIntegral(instantiator.transform(a))
    }
  }

  /** Constraint on type(s). */
  abstract class Constraint(val types: Seq[Type])
  case class Equal(a: Type, b: Type) extends Constraint(Seq(a, b))
  case class Subtype(sub: Type, sup: Type) extends Constraint(Seq(sub, sup))
  case class IsNumeric(a: Type) extends Constraint(Seq(a))
  case class IsComparable(a: Type) extends Constraint(Seq(a))
  case class IsIntegral(a: Type) extends Constraint(Seq(a))
  case class IsBitVector(a: Type) extends Constraint(Seq(a))
  case class AtIndexEqual(tup: Type, mem: Type, idx: Int) extends Constraint(Seq(tup, mem))

  object Constraint {
    def equal(a: Type, b: Type): Constraint = Equal(a, b)
    def subtype(a: Type, b: Type): Constraint = Subtype(a, b)
    def isNumeric(a: Type): Constraint = IsNumeric(a)
    def isIntegral(a: Type): Constraint = IsIntegral(a)
    def isComparable(a: Type): Constraint = IsComparable(a)
    def isBitVector(a: Type): Constraint = IsBitVector(a)
    def atIndex(tup: Type, mem: Type, idx: Int) = AtIndexEqual(tup, mem, idx)
  }

  /** Represents a set of constraints with a value.
   *
   * The value contained is not directly available,
   * but can be obtained from a `Unifier`.
   *
   * Such a `Unifier` should be obtained by solving the constraints.
   *
   * This class offers an applicative functor interface.
   */
  sealed abstract class Constrained[+A] {

    def map[B](f: A => B): Constrained[B] = this match {
      case WithConstraints(v, cs) => WithConstraints(v andThen f, cs)
      case Unsatifiable => Unsatifiable
    }

    def combine[B, C](that: Constrained[B])(f: (A, B) => C): Constrained[C] = (this, that) match {
      case (WithConstraints(vA, csA), WithConstraints(vB, csB)) => WithConstraints((u: Unifier) => f(vA(u), vB(u)), csA ++ csB)
      case (_, _) => Unsatifiable 
    }

    def app[B, C](that: Constrained[B])(implicit ev: A <:< (B => C)): Constrained[C] =
      this.combine(that)((f: A, x: B) => ev(f)(x))

    def get(implicit unifier: Unifier): A = this match {
      case WithConstraints(vA, cs) => vA(unifier)
      case Unsatifiable => throw new Exception("Unsatifiable.get")
    }

    def addConstraint(constraint: => Constraint): Constrained[A] = addConstraints(Seq(constraint))

    def addConstraints(constraints: => Seq[Constraint]): Constrained[A] = this match {
      case WithConstraints(vA, cs) => WithConstraints(vA, constraints ++ cs)
      case Unsatifiable => Unsatifiable
    }
    def checkImmediate(condition: => Boolean): Constrained[A] = this match {
      case Unsatifiable => Unsatifiable
      case _ => if (condition) this else Unsatifiable
    }
  }
  case object Unsatifiable extends Constrained[Nothing]
  case class WithConstraints[A](value: Unifier => A, constraints: Seq[Constraint]) extends Constrained[A]

  object Constrained {
    val fail = Unsatifiable
    def pure[A](x: A): Constrained[A] = WithConstraints((u: Unifier) => x, Seq())
    def withUnifier[A](f: Unifier => A) = WithConstraints(f, Seq())

    def sequence[A](cs: Seq[Constrained[A]]): Constrained[Seq[A]] = {
      val zero: Constrained[Seq[A]] = pure(Seq[A]())
      val cons: (A, Seq[A]) => Seq[A] = (x: A, xs: Seq[A]) => x +: xs

      cs.foldRight(zero) {
        case (c, acc) => c.combine(acc)(cons)
      }
    }
  }
}