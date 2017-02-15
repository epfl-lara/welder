
import sbt._

object WelderBuild extends Build {

  lazy val root = Project("root", file(".")) dependsOn(inoxProject)
  lazy val inoxProject = RootProject(uri("git://github.com/epfl-lara/inox.git#4cc08b0ba91ad9ea7355be92857de6ead66f92ad"))

}