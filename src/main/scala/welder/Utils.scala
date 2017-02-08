/* Copyright 2017 EPFL, Lausanne */

package welder

object Utils {
  
  def oneHole[A](xs: Seq[A]): Seq[(A, Seq[A])] = {

    def go(as: Seq[A], bs: Seq[A]): Seq[(A, Seq[A])] = if (bs.isEmpty) {
      Seq()
    } else {
      (bs.head, as ++ bs.tail) +: go(as :+ bs.head, bs.tail)
    }

    go(Seq(), xs)
  }
}