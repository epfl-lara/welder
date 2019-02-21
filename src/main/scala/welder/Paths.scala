/* Copyright 2017 EPFL, Lausanne */

package welder

import scala.reflect.ClassTag

/** Contains definitions related to paths within expressions. */
trait Paths { self: Theory =>
  
  import program.trees._

  /** Contains an expression and a context. */
  trait Focus {

    /** The expression without its context. */
    val get: Expr

    /** Function to embbed an expression within the context.
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

  /** Defines the next subexpressions on a `Path`. */
  sealed trait Selector {
    def select(expr: Expr, subexprs: Seq[Expr]): Stream[Int]
  }

  /** Selects the child at position `i`. `0`-indexed. */
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

  /** Selects the children at all given positions. `0`-indexed. */
  def children(i: Int, js: Int*): Selector = new Selector {
    def select(expr: Expr, subexprs: Seq[Expr]): Stream[Int] = {
      (i +: js).toStream.filter((x: Int) => x >= 0 && x < subexprs.size)
    }
  }

  /** Selects the children in the given range. `0`-indexed. */
  def children(range: Range): Selector = new Selector {
    def select(expr: Expr, subexprs: Seq[Expr]): Stream[Int] = {
      range.toStream.dropWhile(_ < 0).takeWhile(_ < subexprs.size)
    }
  }

  /** Predicate on expressions. Used within the context of `Path`s. */
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

  /** Describes all expressions of the given type `T`. */
  def is[T <: Expr](implicit ct: ClassTag[T]): Descriptor = new Descriptor {
    def describes(expr: Expr): Boolean = ct.runtimeClass.isInstance(expr)
  }

  /** Describes the expression `expr`. */
  def is(expr: Expr): Descriptor = new Descriptor {
    def describes(e: Expr): Boolean = expr == e
  }

  /** Describes a path within an expression. */
  sealed trait Path {

    /** The prefix of the path. */
    protected val previous: Option[Path]

    /** The stream of focuses described by the path. */
    protected def focuses(expr: Expr): Stream[Focus] 

    /** Applies a path to an expression. */
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

    /** Describes which branches to match in the next level. */
    def ~(descriptor: Descriptor): Path = {
      val thiz = this

      new Path {
        protected override val previous = Some(thiz)

        protected override def focuses(expr: Expr): Stream[Focus] = {
          val (is, vs, es, ts, fs, builder) = deconstructor.deconstruct(expr)

          es.toStream.zip(Stream.from(0)).flatMap { case (e, index) =>
            if (descriptor.describes(e)) {
              Stream(new Focus {
                val get = e
                def set(e: Expr) = builder(is, vs, es.updated(index, e), ts, fs)
              })
            }
            else {
              Stream()
            }
          }
        }
      }
    }

    /** Selects which branches to match in the next level. */
    def ~(selector: Selector): Path = {
      val thiz = this

      new Path {
        protected override val previous = Some(thiz)

        protected override def focuses(expr: Expr): Stream[Focus] = {
          val (is, vs, es, ts, fs, builder) = deconstructor.deconstruct(expr)


          selector.select(expr, es) map { (index: Int) =>
            new Focus {
              val get = es(index)
              def set(e: Expr) = builder(is, vs, es.updated(index, e), ts, fs)
            }
          }
        }
      }
    }

    /** Describes all expressions to match, at any depth. */
    def ~~(descriptor: Descriptor): Path = {
      val thiz = this

      new Path {
        protected override val previous = Some(thiz)

        protected override def focuses(expr: Expr): Stream[Focus] = {
          val (is, vs, es, ts, fs, builder) = deconstructor.deconstruct(expr)

          es.toStream.zip(Stream.from(0)).flatMap { case (e, index) =>

            def rest = focuses(e).map { (f: Focus) =>
              new Focus {
                val get = f.get
                def set(inner: Expr) = builder(is, vs, es.updated(index, f.set(inner)), ts, fs)
              }
            }

            if (descriptor.describes(e)) {
              val focus = new Focus {
                val get = e
                def set(inner: Expr) = builder(is, vs, es.updated(index, inner), ts, fs)
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

    /** Selects a specified alternative. */
    def |(index: Int): Path = {
      val thiz = this

      new Path {
        protected override val previous = thiz.previous

        protected override def focuses(expr: Expr): Stream[Focus] = {
          thiz.focuses(expr).slice(index, index + 1)
        }
      }
    }

    /** Selects only paths that end on expressions satisfying the descriptor. */
    def |(descriptor: Descriptor): Path = {
      val thiz = this

      new Path {
        protected override val previous = thiz.previous

        protected override def focuses(expr: Expr): Stream[Focus] = {
          thiz.focuses(expr).filter((f: Focus) => descriptor.describes(f.get))
        }
      }
    }
  }

  /** Matches to entirety of an expression. */
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