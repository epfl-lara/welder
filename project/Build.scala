
import sbt._

object WelderBuild extends Build {

  lazy val root = Project("root", file(".")) dependsOn(inoxProject)
  lazy val inoxProject = RootProject(uri("git://github.com/epfl-lara/inox.git#78ab430ccc9cc1fe45bcaae864fb129f7fa542fe"))

}