
import sbt._

object WelderBuild extends Build {

  lazy val root = Project("root", file(".")) dependsOn(inoxProject)
  lazy val inoxProject = RootProject(uri("git://github.com/epfl-lara/inox.git#8c7e0b760f65a5fad5c14cbe263a489476ee2dd7"))

}