package welder
package parsing

import inox.InoxProgram

trait Interpolator extends BuiltIns
                      with Constraints
                      with TypeIRs
                      with ExprIRs
                      with ConstraintSolvers
                      with Lexers
                      with TypeParsers
                      with ExpressionParsers {

  val program: InoxProgram
}