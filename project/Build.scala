
import sbt._

object WelderBuild extends Build {

  lazy val root = Project("root", file(".")) dependsOn(inoxProject)
  lazy val inoxProject = RootProject(uri("git://github.com/epfl-lara/inox.git#68f9b0856c3be1cf63313a6b6ad7b67fa4abe323"))

}