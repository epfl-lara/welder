package welder
package parsing

sealed abstract class Assoc
case object LeftAssoc extends Assoc
case object RightAssoc extends Assoc
case object AnyAssoc extends Assoc