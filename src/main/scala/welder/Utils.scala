/* Copyright 2017 EPFL, Lausanne */

package welder

import scala.collection.BitSet

object Utils {
  
  def oneHole[A](xs: Seq[A]): Seq[(A, Seq[A])] = {

    def go(as: Seq[A], bs: Seq[A]): Seq[(A, Seq[A])] = if (bs.isEmpty) {
      Seq()
    } else {
      (bs.head, as ++ bs.tail) +: go(as :+ bs.head, bs.tail)
    }

    go(Seq(), xs)
  }

  def traverse[A](xs: Seq[Option[A]]): Option[Seq[A]] = {
    val zero: Option[Seq[A]] = Some(Seq[A]())

    xs.foldRight(zero) {
      case (Some(x), Some(xs)) => Some(x +: xs)
      case _ => None
    }
  }

  def toFraction(string: String): (BigInt, BigInt) = {
    val parts = string.split('.')

    val size = parts.length
    require(size == 1 || size == 2, "toFraction: Not a valid formatted number.")

    val nominator = BigInt(parts.reduce(_ ++ _))
    val denominator = if (size == 2) BigInt(10).pow(parts(1).length) else BigInt(1)
    val gcd = nominator.gcd(denominator)

    (nominator / gcd, denominator / gcd)
  }

  def toPartial[A <: AnyRef, B](f: A => Option[B]): PartialFunction[A, B] = {
    val argCache = new ThreadLocal[A]
    val resultCache = new ThreadLocal[Option[B]] {
      override def initialValue() = None
    }

    {
      case a if { 
        if (!(argCache.get eq a)) {
          argCache.set(a)
          val optB = f(a)
          resultCache.set(optB)
          optB.isDefined
        }
        else {
          resultCache.get.isDefined
        }
      } => {
        resultCache.get.get
      }
    }
  }
}