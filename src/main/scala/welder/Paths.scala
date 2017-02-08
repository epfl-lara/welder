/* Copyright 2017 EPFL, Lausanne */

package welder

import scala.reflect.ClassTag

import inox._
import inox.ast._

trait Paths { self: Theory =>
  
  import program.trees._

  /** Models an expression within a context. */
  trait Focus {

    /** The expression without its context. */
    val get: Expr

    /** The context.
     *
     * @param replacement An expression to embed in the context.
     * @return The `replacement`, embedded in the context.
     */
    def set(replacement: Expr): Expr

    /** Modifies the expression within its context.
     *
     * @param f The function to apply on the focused expression.
     * @return The application of `f` to the focused expression,
     *         in the context.
     */
    def modify(f: Expr => Expr) = set(f(get))

    override def toString(): String = {
      val hole = Variable.fresh("_", get.getType)
      val context = set(hole)

      "Focus(on=" + get + ", context=" + context + ")"
    }
  }

  // TODO:
  // rhs / lhs
  // child(i)
  // children(i, j*)
  // children(Range[..])

  sealed trait Selector {
    def select(expr: Expr, subexprs: Seq[Expr]): Stream[Int]
  }

  def child(i: Int): Selector = new Selector {

    def select(expr: Expr, subexprs: Seq[Expr]): Stream[Int] = {
      if (i >= 0 && i < subexprs.size) {
        Stream(i)
      }
      else {
        Stream()
      }
    }
  }

  sealed trait Descriptor {
    def describes(expr: Expr): Boolean

    def ||(that: Descriptor): Descriptor = {
      val thiz = this

      new Descriptor {
        def describes(expr: Expr): Boolean =
          thiz.describes(expr) || that.describes(expr)
      }
    }
  }

  def is[T <: Expr](implicit ct: ClassTag[T]): Descriptor = new Descriptor {
    def describes(expr: Expr): Boolean = ct.runtimeClass.isInstance(expr)
  }

  def is(x: Expr): Descriptor = new Descriptor {
    def describes(expr: Expr): Boolean = x == expr
  }

  sealed trait Path {

    protected val previous: Option[Path]
    protected def focuses(expr: Expr): Stream[Focus] 

    def on(expression: Expr): Stream[Focus] = {

      previous match {
        case None => focuses(expression)
        case Some(path) => {
          path.on(expression).flatMap {
            (f: Focus) => focuses(f.get).map {
              (g: Focus) => new Focus {
                val get = g.get
                def set(inner: Expr): Expr = f.set(g.set(inner))
              }
            }
          }
        }
      }
    }

    def ~(descriptor: Descriptor): Path = {
      val thiz = this

      new Path {
        protected override val previous = Some(thiz)

        protected override def focuses(expr: Expr): Stream[Focus] = {
          val (vs, es, ts, builder) = deconstructor.deconstruct(expr)

          es.toStream.zip(Stream.from(0)).flatMap { case (e, index) =>
            if (descriptor.describes(e)) {
              Stream(new Focus {
                val get = e
                def set(e: Expr) = builder(vs, es.updated(index, e), ts)
              })
            }
            else {
              Stream()
            }
          }
        }
      }
    }

    def ~(selector: Selector): Path = {
      val thiz = this

      new Path {
        protected override val previous = Some(thiz)

        protected override def focuses(expr: Expr): Stream[Focus] = {
          val (vs, es, ts, builder) = deconstructor.deconstruct(expr)


          selector.select(expr, es) map { (index: Int) =>
            new Focus {
              val get = es(index)
              def set(e: Expr) = builder(vs, es.updated(index, e), ts)
            }
          }
        }
      }
    }

    def ~~(descriptor: Descriptor): Path = {
      val thiz = this

      new Path {
        protected override val previous = Some(thiz)

        protected override def focuses(expr: Expr): Stream[Focus] = {
          val (vs, es, ts, builder) = deconstructor.deconstruct(expr)

          es.toStream.zip(Stream.from(0)).flatMap { case (e, index) =>

            def rest = focuses(e).map { (f: Focus) =>
              new Focus {
                val get = f.get
                def set(inner: Expr) = builder(vs, es.updated(index, f.set(inner)), ts)
              }
            }

            if (descriptor.describes(e)) {
              val focus = new Focus {
                val get = e
                def set(inner: Expr) = builder(vs, es.updated(index, inner), ts)
              }

              focus +: rest
            }
            else {
              rest
            }
          }
        }
      }
    }

    def |(index: Int): Path = {
      val thiz = this

      new Path {
        protected override val previous = thiz.previous

        protected override def focuses(expr: Expr): Stream[Focus] = {
          thiz.focuses(expr).drop(index).take(1)
        }
      }
    }
  }

  lazy val root = new Path {

    protected override val previous: Option[Path] = None

    protected override def focuses(expr: Expr): Stream[Focus] = {
      
      val focus = new Focus {
        val get = expr
        def set(e: Expr) = e
      }

      Stream(focus)
    }
  } 
}