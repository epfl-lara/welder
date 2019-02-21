/* Copyright 2017 EPFL, Lausanne */

import inox._

package object welder {
  
  case object DebugSectionWelder extends DebugSection("welder")


  def theoryOf(pgm: InoxProgram): Theory = new Theory {
    override val program = pgm
    override val ctx = Context.empty
  }
} 