package welder
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input._

/** Contains methods for lexical parsing of StringContext objects and their arguments. */
trait StringContextLexer extends { self: Lexical =>
  
  /** Converts an argument of the StringContext to a Token. */
  def argToToken(x: Any): Token

  /** Returns a reader from a StringContext and its arguments. */
  def getReader(sc: StringContext, args: Seq[Any]): Reader[Token] = {
    require(sc.parts.size == args.size + 1, "Wrong number of arguments.")

    // For string parts, we can create a Scanner.
    val stringReaders = sc.parts.map(new Scanner(_))
    
    // All readers (both for parts and args).
    val readers = if (args.isEmpty) {

      // Only string readers in this case.
      stringReaders
    } else {

      // Turns all args into readers.
      val argsReaders = args.map(toMetaReader(_))

      // Intercalates argsReaders between stringReaders.
      stringReaders.head +: {
        argsReaders.zip(stringReaders.tail).flatMap {
          case (argReader, stringReader) => Seq(argReader, stringReader)
        }
      }
    }

    // Sequences all readers into a single one.
    readers.reduce(sequenceReader(_, _))
  }

  /** Turns any value to a reader that produces the associated token. */
  private def toMetaReader(value: Any) = new Reader[Token] {
    override def atEnd: Boolean = false
    override def first: Token = argToToken(value)
    override def pos: Position = NoPosition
    override def rest: Reader[Token] = new Reader[Token] {
      override def atEnd: Boolean = true
      override def pos: Position = ???
      override def first: Token = ???
      override def rest: Reader[Token] = ???
    }
  }

  /** Sequences two readers. */
  private def sequenceReader(a: Reader[Token], b: => Reader[Token]): Reader[Token] = {

    if (a.atEnd) {
      b
    }
    else {
      new Reader[Token] {
        override def atEnd: Boolean = false
        override def first: Token = a.first
        override def pos: Position = a.pos
        override def rest: Reader[Token] = {
          sequenceReader(a.rest, b)
        }
      }
    }
  }
} 