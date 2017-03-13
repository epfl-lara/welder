
import sbt._

object WelderBuild extends Build {

  lazy val root = Project("root", file(".")) dependsOn(inoxProject)
  lazy val inoxProject = RootProject(uri("git://github.com/epfl-lara/inox.git#32935b45d1ab32c64ac804b10185d7a1aa17838b"))

}