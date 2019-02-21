
import inox._
import inox.trees._
import inox.trees.interpolator._
import welder._

/** This example contains the definition of two ADTs, Lists and Trees,
 *  along with functions to manipulate such data types.
 *
 * The example also contains various theorems on Lists and Trees.
 * The main theorem of this example states that applying fold on two Trees
 * with the same toList representation yields the same result.
 */
object ListsAndTrees {

  // First part, definition of the various definitions of the program.

  val definitions = p"""
    type List[A] = Cons(head: A, tail: List[A]) | Nil()

    def concat[A](xs: List[A], ys: List[A]): List[A] =
      if (xs is Nil) ys else Cons(xs.head, concat(xs.tail, ys))

    def listMap[A, B](xs: List[A], f: A => B): List[B] =
      if (xs is Nil) Nil() else Cons(f(xs.head), listMap(xs.tail, f))

    def listFold[A](xs: List[A], f: (A, A) => A): A =
      if (xs.tail is Nil) xs.head else f(xs.head, listFold(xs.tail, f))

    type Tree[A] = Branch(left: Tree[A], right: Tree[A]) | Leaf(value: A)

    def toList[A](t: Tree[A]): List[A] =
      if (t is Leaf) Cons(t.value, Nil()) else concat(toList(t.left), toList(t.right))

    def treeMap[A, B](t: Tree[A], f: A => B): Tree[B] =
      if (t is Leaf) Leaf(f(t.value)) else Branch(treeMap(t.left, f), treeMap(t.right, f))

    def treeFold[A](t: Tree[A], f: (A, A) => A): A =
      if (t is Leaf) t.value else f(treeFold(t.left, f), treeFold(t.right, f))
    """

  // Definition of the program.
  val program: InoxProgram = Program(inox.trees)(NoSymbols
    .withFunctions(definitions.collect { case d: FunDef => d })
    .withSorts(definitions.collect { case d: ADTSort => d }))

  // The Inox-only part is over now... Introducing welder!


  // Creating and importing the theory of the program.  
  val theory: Theory = theoryOf(program)
  import theory._

  // Creating two type parameters.
  val tA: TypeParameter = TypeParameter.fresh("A")
  val tB: TypeParameter = TypeParameter.fresh("B")

  // Theorem stating that listMap(f, as) ++ listMap(f, bs) == listMap(f, as ++ bs)
  lazy val mapCommutesWithConcatenate: Theorem = forallI(vd"f: $tA => $tB", vd"bs: List[$tA]") { case (f, bs) =>
    def mapCommutes(as: Expr) =
      e"listMap(concat($as, $bs), $f) == concat(listMap($as, $f), listMap($bs, $f))"

    structuralInduction(mapCommutes _, vd"xs: List[$tA]") { case (ihs, goal) =>
      ihs.expression match {
        case e"Cons($_, $xs)" => ihs.hypothesis(xs)
        case e"Nil()" => trivial
      }
    } 
  }

  // Theorem stating that toList(treeMap(t) == listMap(toList(t))
  lazy val mapCommutesWithToList: Theorem = forallI(vd"f: $tA => $tB") { f =>

    def mapCommutes(t: Expr) =
      e"toList(treeMap($t, $f)) == listMap(toList($t), $f)"

    structuralInduction(mapCommutes _, vd"t: Tree[$tA]") { case (ihs, _) =>
      ihs.expression match {
        case e"Branch($l, $r)" => {
          andI(ihs.hypothesis(l), ihs.hypothesis(r), mapCommutesWithConcatenate)
        }
        case e"Leaf($_)" => trivial
      }
    }
  }

  // Definition of the associativity.
  def isAssoc(f: Expr) = e"forall (a, b, c) => ($f)(a, ($f)(b, c)) == ($f)(($f)(a, b), c)"

  // Theorem stating that, for any two non-empty lists xs and ys, and associative function f,
  // the following holds: listFold(xs ++ ys, f) == f(listFold(xs, f), listFold(ys, f))
  lazy val splitListFold = forallI(vd"f: ($tA, $tA) => $tA", vd"ys: List[$tA]") { case (f, ys) =>
    implI(isAssoc(f)) { fIsAssoc: Theorem =>
      implI(e"$ys is Cons") { ysNonEmpty: Theorem =>

        def lhs(xs: Expr) = e"listFold(concat($xs, $ys), $f)"
        def rhs(xs: Expr) = e"($f)(listFold($xs, $f), listFold($ys, $f))"

        def property(xs: Expr) =
          e"$xs is Cons ==> (${lhs(xs)} == ${rhs(xs)})"

        structuralInduction(property _, vd"xs: List[$tA]") { case (ihs, _) =>
          ihs.expression match {
            case e"Cons($h, $t)" => {

              val tIsNonEmptyCase: Theorem = implI(e"$t is Cons") { tNonEmpty: Theorem =>

                lhs(ihs.expression)                                           ==|
                                                                     ysNonEmpty |
                e"listFold(Cons($h, concat($t, $ys)), $f)"                    ==|
                                                                     ysNonEmpty |
                e"($f)($h, listFold(concat($t, $ys), $f))"                    ==|
                                 andI(ihs.hypothesis(t), tNonEmpty, ysNonEmpty) |
                e"($f)($h, ($f)(listFold($t, $f), listFold($ys, $f)))"        ==|
                                          andI(fIsAssoc, tNonEmpty, ysNonEmpty) |
                e"($f)(($f)($h, listFold($t, $f)), listFold($ys, $f))"        ==|
                                                    andI(tNonEmpty, ysNonEmpty) |
                rhs(ihs.expression)
              }

              val tIsEmptyCase: Theorem = implI(e"$t is Nil") { tEmpty: Theorem =>

                lhs(ihs.expression)                                           ==|
                                                                        trivial |
                e"listFold(Cons($h, concat($t, $ys)), $f)"                    ==|
                                                                     ysNonEmpty |
                e"($f)($h, listFold(concat($t, $ys), $f))"                    ==|
                                                       andI(tEmpty, ysNonEmpty) |
                e"($f)($h, listFold($ys, $f))"                                ==|
                                                       andI(tEmpty, ysNonEmpty) |
                rhs(ihs.expression)
              }

              andI(tIsNonEmptyCase, tIsEmptyCase)
            }
            case e"Nil()" => trivial
          }
        }
      }
    }
  }


  // Theorem stating that the result of toList is non-empty.
  lazy val toListNonEmpty: Theorem = {
    def property(t: Expr) = e"toList($t) is Cons"

    structuralInduction(property _, vd"t: Tree[$tA]") { case (ihs, _) =>
      ihs.expression match {
        case e"Branch($l, $r)" => andI(ihs.hypothesis(l), ihs.hypothesis(r))
        case e"Leaf($_)" => trivial
      }
    }
  }

  // Theorem stating that for all associative function f and tree t,
  // the following holds: treeFold(t, f) == listFold(toList(t), f)
  lazy val foldTheorem: Theorem = forallI(vd"f: ($tA, $tA) => $tA") { f =>
    implI(isAssoc(f)) { fIsAssoc: Theorem =>
      def property(t: Expr) = e"treeFold($t, $f) == listFold(toList($t), $f)"

      structuralInduction(property _, vd"t: Tree[$tA]") { case (ihs, _) =>
        ihs.expression match {
          case e"Branch($l, $r)" => {

            val splitListFoldInstantiated = splitListFold
              .forallE(f, e"toList($r)")
              .implE(_.by(fIsAssoc))
              .implE(_.by(toListNonEmpty))
              .forallE(e"toList($l)")
              .implE(_.by(toListNonEmpty))

            e"treeFold(Branch($l, $r), $f)"                                               ==|
                                                                                    trivial |
            e"($f)(treeFold($l, $f), treeFold($r, $f))"                                   ==|
                                                                          ihs.hypothesis(l) |
            e"($f)(listFold(toList($l), $f), treeFold($r, $f))"                           ==|
                                                                          ihs.hypothesis(r) |
            e"($f)(listFold(toList($l), $f), listFold(toList($r), $f))"                   ==|
                                                                  splitListFoldInstantiated |
            e"listFold(concat(toList($l), toList($r)), $f)"                               ==|
                                                                                    trivial |
            e"listFold(toList(Branch($l, $r)), $f)"
          }
          case e"Leaf($_)" => trivial
        }
      }
    }
  }


  // Reformulation of the previous theorem. It now reads:
  // forall trees t1 and t2, and associative function f, if toList(t1) == toList(t2) then
  // treeFold(t1, f) == treeFold(t2, f)
  lazy val reformulatedFoldTheorem: Theorem = forallI(vd"f: ($tA, $tA) => $tA") { f =>
    implI(isAssoc(f)) { fIsAssoc: Theorem =>
      forallI(vd"t1: Tree[$tA]", vd"t2: Tree[$tA]") { case (t1, t2) =>
        implI(e"toList($t1) == toList($t2)") { tsEqual: Theorem =>

          val applied1 = forallE(implE(forallE(foldTheorem)(f))(_.by(fIsAssoc)))(t1)
          val applied2 = forallE(implE(forallE(foldTheorem)(f))(_.by(fIsAssoc)))(t2)

          e"treeFold($t1, $f)"                  ==|
                                         applied1 |
          e"listFold(toList($t1), $f)"          ==|
                                          tsEqual |
          e"listFold(toList($t2), $f)"          ==|
                                         applied2 |
          e"treeFold($t2, $f)"
        }
      }
    }
  }
}
