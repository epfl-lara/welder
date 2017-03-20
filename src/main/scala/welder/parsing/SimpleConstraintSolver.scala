package welder
package parsing

import inox.InoxProgram

class SimpleConstraintSolver(val program: InoxProgram) {

  val constraints = new Constraints {
    override val trees = program.trees
    override val symbols = program.symbols
  }

  import program.trees._
  import constraints._

  case class Bounds(lowers: Set[Type], uppers: Set[Type])

  object UnknownChecker {
    var exists = false

    val traverser = new TreeTraverser {
      override def traverse(t: Type) {
        t match {
          case _: Unknown => exists = true
          case _ => super.traverse(t)
        } 
      }
    }

    def apply(t: Type): Boolean = {
      exists = false
      traverser.traverse(t)
      exists
    }
  }

  class OccurChecker(u: Unknown) {
    var exists = false

    val traverser = new TreeTraverser {
      override def traverse(t: Type) {
        t match {
          case u2: Unknown => {
            if (u == u2) exists = true
          }
          case _ => {
            super.traverse(t)
          }
        } 
      }
    }

    def apply(t: Type): Boolean = {
      exists = false
      traverser.traverse(t)
      exists
    }
  }

  def solveConstraints(constraints: Seq[Constraint]): Option[Unifier] = {

    var remaining: Seq[Constraint] = constraints
    var substitutions: Map[Unknown, Type] = Map()
    var bounds: Map[Unknown, Bounds] = Map()
    var typeClasses: Map[Unknown, Constraint] = Map()
    var tupleConstraints: Map[Unknown, Set[Constraint]] = Map()

    def substitute(u: Unknown, t: Type) {
      val subst = new Unifier(Map(u -> t))

      remaining = remaining.map(subst(_))
      substitutions = substitutions.mapValues(subst(_))
      substitutions += (u -> t)
      tupleConstraints = tupleConstraints.mapValues(_.map(subst(_)))
      typeClasses = typeClasses.mapValues(subst(_))

      bounds = bounds.mapValues {
        case Bounds(ls, us) => Bounds(ls.map(subst(_)), us.map(subst(_)))
      }

      // If the variable we are substituting has bounds...
      bounds.get(u).foreach {

        // We reintroduce those bounds has constraints.
        case Bounds(ls, us) => {
          remaining ++= ls.map(Subtype(_, t))
          remaining ++= us.map(Subtype(t, _))
        }

        // We remove the bounds of the variable.
        bounds -= u
      }

      // If the variable we are substituting has "tuple" constraints...
      tupleConstraints.get(u).foreach { (cs: Set[Constraint]) =>

        // We reintroduce those constraints.
        remaining ++= cs

        // Remove the entry for the variable.
        tupleConstraints -= u
      }

      // If the variable we are substituting has a class constraint...
      typeClasses.get(u).foreach { (c: Constraint) =>

        // We reintroduce this constraints.
        remaining +:= c

        // Remove the entry for the variable.
        typeClasses -= u
      }
    }

    def verifyBounds(b: Bounds) {

    }

    def isSurelyEnd(tpe: Type, top: Boolean): Boolean = tpe match {
      case _: Unknown => false
      case NAryType(Seq(), _) => true
      case ADTType(id, tps) => {
        val adtDef = symbols.getADT(id)
        assert(tps.length == tps.length)

        val sortCorrect = if (top) {
          adtDef.root(symbols) == adtDef
        }
        else {
          adtDef.root(symbols) != adtDef || {
            adtDef.isInstanceOf[ADTSort] &&
            adtDef.asInstanceOf[ADTSort].cons.isEmpty
          }
        }

        sortCorrect && {
          adtDef.tparams.zip(tps).forall {
            case (tpDef, argTpe) => {
              if (tpDef.tp.isCovariant) {
                isSurelyEnd(argTpe, top)
              }
              else if (tpDef.tp.isContravariant) {
                isSurelyEnd(argTpe, !top)
              }
              else {
                true
              }
            }
          }
        }
      }
      case TupleType(ts) => ts.forall(isSurelyEnd(_, top))
      case FunctionType(fs, t) => fs.forall(isSurelyEnd(_, !top)) && isSurelyEnd(t, top)
      case BagType(_) | SetType(_) | MapType(_, _) => true // Those are invariant.
    }

    def strongerClass(a: Constraint, b: Constraint) = (a, b) match {
      case (IsBitVector(_), _) => a
      case (_, IsBitVector(_)) => b
      case (IsIntegral(_), _) => a
      case (_, IsIntegral(_)) => b
      case (IsNumeric(_), _) => a
      case (_, IsNumeric(_)) => b
      case (IsComparable(_), _) => a
      case (_, IsComparable(_)) => b
    }

    def handle(constraint: Constraint) {
      constraint match {
        case Equal(a, b) => (a, b) match {
          case _ if (a == b) => ()
          case (u1: Unknown, u2: Unknown) => {
            substitute(u1, u2)
          }
          case (u: Unknown, t) => {
            val checker = new OccurChecker(u)
            if (checker(t)) {
              throw new Exception("Occur check.")
            }

            substitute(u, t)
          }
          case (t, u: Unknown) => {
            val checker = new OccurChecker(u)
            if (checker(t)) {
              throw new Exception("Occur check.")
            }

            substitute(u, t)
          }
          case (FunctionType(fas, ta), FunctionType(fbs, tb)) if (fbs.length == fas.length) => {
            remaining ++= fas.zip(fbs).map({ case (fa, fb) => Equal(fa, fb) })
            remaining +:= Equal(ta, tb)
          } 
          case (TupleType(tas), TupleType(tbs)) if (tas.length == tbs.length) => {
            remaining ++= tas.zip(tbs).map({ case (ta, tb) => Equal(ta, tb) })
          }
          case (ADTType(ida, tas), ADTType(idb, tbs)) if (ida == idb && tas.length == tbs.length) => {
            remaining ++= tas.zip(tbs).map({ case (ta, tb) => Equal(ta, tb) })
          }
          case (SetType(ta), SetType(tb)) => {
            remaining +:= Equal(ta, tb)
          }
          case (BagType(ta), BagType(tb)) => {
            remaining +:= Equal(ta, tb)
          }
          case (MapType(fa, ta), MapType(fb, tb)) => {
            remaining +:= Equal(fa, fb)
            remaining +:= Equal(ta, tb)
          }
          case _ => throw new Exception("Types incompatible: " + a + ", " + b)
        }
        case Subtype(a, b) => (a, b) match {
          case _ if (a == b) => ()
          case (u1: Unknown, u2: Unknown) => {
            val Bounds(l1s, u1s) = bounds.get(u1).getOrElse(Bounds(Set(), Set()))
            val Bounds(l2s, u2s) = bounds.get(u2).getOrElse(Bounds(Set(), Set()))

            bounds += (u1 -> Bounds(l1s, u1s + u2))
            bounds += (u2 -> Bounds(l2s + u1, u2s))
          }
          case (u: Unknown, _) => {
            val checker = new OccurChecker(u)
            if (checker(b)) {
              throw new Exception("Occur check.")
            }

            if (isSurelyEnd(b, false)) {
              // If b is at the bottom of the subtyping chain...
              remaining +:= Equal(a, b)
            }
            else {
              val Bounds(ls, us) = bounds.get(u).getOrElse(Bounds(Set(), Set()))
              val nBounds = Bounds(ls, us + b)
              verifyBounds(nBounds)
              bounds += (u -> nBounds)
            }
          }
          case (_, u: Unknown) => {
            val checker = new OccurChecker(u)
            if (checker(a)) {
              throw new Exception("Occur check.")
            }

            if (isSurelyEnd(a, true)) {
              // If a is at the top of the subtyping chain...
              remaining +:= Equal(a, b)
            }
            else {
              val Bounds(ls, us) = bounds.get(u).getOrElse(Bounds(Set(), Set()))
              val nBounds = Bounds(ls + a, us)
              verifyBounds(nBounds)
              bounds += (u -> nBounds)
            }
          }
          case (ADTType(id1, t1s), ADTType(id2, t2s)) => {
            val adtDef1 = symbols.lookupADT(id1).getOrElse {
              throw new Error("Unknown ADT: " + id1)
            }

            val adtDef2 = symbols.lookupADT(id2).getOrElse {
              throw new Error("Unknown ADT: " + id2)
            }

            if (adtDef1 != adtDef2 && adtDef1.root(symbols) != adtDef2) {
              throw new Exception("Type " + a + " can not be a subtype of " + b)
            }

            if (t1s.length != t2s.length || t2s.length != adtDef1.tparams.length) {
              throw new Exception("Type " + a + " can not be a subtype of " + b)
            }

            assert(adtDef1.tparams.length == adtDef2.tparams.length)
            assert(adtDef1.tparams.zip(adtDef2.tparams).forall({
              case (tp1, tp2) => (tp1.tp.isCovariant == tp2.tp.isCovariant) &&
                                 (tp1.tp.isContravariant == tp2.tp.isContravariant) &&
                                 (tp1.tp.isInvariant == tp2.tp.isInvariant)
            }))

            adtDef1.tparams.zip(t1s.zip(t2s)).foreach {
              case (tpDef, (t1, t2)) => {
                if (tpDef.tp.isCovariant) {
                  remaining +:= Subtype(t1, t2)
                }
                if (tpDef.tp.isContravariant) {
                  remaining +:= Subtype(t2, t1)
                }
                if (tpDef.tp.isInvariant) {
                  remaining +:= Equal(t1, t2)
                }
              }
            }
          }
          case (TupleType(tas), TupleType(tbs)) if (tas.length == tbs.length) => {
            tas.zip(tbs).foreach {
              case (ta, tb) => remaining +:= Subtype(ta, tb)
            }
          }
          case (SetType(ta), SetType(tb)) => {
            remaining +:= Equal(ta, tb)  // Sets are invariant.
          }
          case (BagType(ta), BagType(tb)) => {
            remaining +:= Equal(ta, tb) // Bags are invariant.
          }
          case (MapType(fa, ta), MapType(fb, tb)) => {
            remaining +:= Equal(fa, fb) // Maps are invariant.
            remaining +:= Equal(ta, tb)
          }
          case (FunctionType(fas, ta), FunctionType(fbs, tb)) if (fas.length == fbs.length) => {
            fas.zip(fbs).foreach {
              case (fa, fb) => remaining +:= Subtype(fb, fa)
            }
            remaining +:= Subtype(ta, tb)
          }
          case (NAryType(Seq(), _), _) => {
            remaining +:= Equal(a, b)
          }
          case (_, NAryType(Seq(), _)) => {
            remaining +:= Equal(a, b)
          }
          case _ => {
            throw new Exception("Type " + a + " can not be a subtype of " + b)
          }
        }
        case AtIndexEqual(a, b, i) => a match {
          case u: Unknown => {
            typeClasses.get(u).foreach {
              case _ => throw new Error("Type " + a + " can not be both a tuple and have classes.")  // TODO: Nicer error message.
            }
            tupleConstraints += (u -> (tupleConstraints.get(u).getOrElse(Set()) + constraint))
          }
          case TupleType(tps) => {
            if (tps.length >= i) {
              remaining +:= Equal(tps(i - 1), b)
            }
            else {
              throw new Exception("Type " + a + " does not have a field at index " + i)
            }
          }
          case _ => {
            throw new Exception("Type " + a + " is not a tuple.")
          }
        }
        case IsBitVector(a) => a match {
          case u: Unknown => {
            bounds.get(u).foreach {
              case Bounds(ls, us) => {
                remaining ++= ls.map(Equal(u, _))  // Member of this type class are flat.
                remaining ++= us.map(Equal(u, _))
              }

              bounds -= u
            }
            tupleConstraints.get(u).foreach {
              case _ => throw new Error("Type " + a + " can not be both a bit vector and a tuple.")
            }
            typeClasses += (u -> { typeClasses.get(u) match {
              case None => constraint
              case Some(c) => strongerClass(constraint, c)
            }})
          }
          case BVType(_) => ()
          case _ => throw new Exception("Type " + a + " is not a bit vector.")
        }
        case IsIntegral(a) => a match {
          case u: Unknown => {
            bounds.get(u).foreach {
              case Bounds(ls, us) => {
                remaining ++= ls.map(Equal(u, _))  // Member of this type class are flat.
                remaining ++= us.map(Equal(u, _))
              }

              bounds -= u
            }
            tupleConstraints.get(u).foreach {
              case _ => throw new Error("Type " + a + " can not be both an integer and a tuple.")
            }
            typeClasses += (u -> { typeClasses.get(u) match {
              case None => constraint
              case Some(c) => strongerClass(constraint, c)
            }})
          }
          case BVType(_) | IntegerType => ()
          case _ => throw new Exception("Type " + a + " is not numeric.")
        }
        case IsNumeric(a) => a match {
          case u: Unknown => {
            bounds.get(u).foreach {
              case Bounds(ls, us) => {
                remaining ++= ls.map(Equal(u, _))  // Member of this type class are flat.
                remaining ++= us.map(Equal(u, _))
              }

              bounds -= u
            }
            tupleConstraints.get(u).foreach {
              case _ => throw new Error("Type " + a + " can not be both numeric and a tuple.")
            }
            typeClasses += (u -> { typeClasses.get(u) match {
              case None => constraint
              case Some(c) => strongerClass(constraint, c)
            }})
          }
          case BVType(_) | RealType | IntegerType => ()
          case _ => throw new Exception("Type " + a + " is not numeric.")
        }
        case IsComparable(a) => a match {
          case u: Unknown => {
            bounds.get(u).foreach {
              case Bounds(ls, us) => {
                remaining ++= ls.map(Equal(u, _))  // Member of this type class are flat.
                remaining ++= us.map(Equal(u, _))
              }

              bounds -= u
            }
            tupleConstraints.get(u).foreach {
              case _ => throw new Error("Type " + a + " can not be both comparable and a tuple.")
            }
            typeClasses += (u -> { typeClasses.get(u) match {
              case None => constraint
              case Some(c) => strongerClass(constraint, c)
            }})
          }
          case BVType(_) | RealType | IntegerType | CharType => ()
          case _ => throw new Exception("Type " + a + " is not comparable.")
        }
      }
    }

    // println(remaining)
    // println("-------------")

    var stop = false

    while (!stop) {
      while (!remaining.isEmpty) {
        val constraint = remaining.head
        remaining = remaining.tail
        // println()
        // println(constraint)
        // println()
        handle(constraint)

        // println("Remaining: " + remaining)
        // println("Bounds: " + bounds)
        // println("Classes: " + typeClasses)
        // println("TupleConstraints: " + tupleConstraints)
      }

      stop = true

      // Set the default instance for classes.
      if (!typeClasses.isEmpty) {

        val defaults = typeClasses.map({
          case (t, IsIntegral(_) | IsNumeric(_)) => Some(Equal(t, IntegerType))  // BigInt by default.
          case (t, IsBitVector(_)) => Some(Equal(t, Int32Type))
          case _ => None
        }).flatten

        if (!defaults.isEmpty) {
          stop = false
          remaining ++= defaults
        }
      }
    }

    // println("-------------")
    // println("Substitution: " + substitutions)

    Some(new Unifier(substitutions))
  }


}