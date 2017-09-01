lazy val root = (project in file("."))
  .dependsOn(jsaiProject)
  .settings(
    scalaVersion := "2.12.2",

    name := "scsc",

    organization := "ch.usi.l3.scsc",

    version := "0.1",

    sourcesInBase := false,

    // allow Ctrl-C to cancel tasks
    cancelable in Global := true,

    // don't run tests in parallel... nashorn parser gets confused
    parallelExecution in Test := false,

    resolvers += Resolver.sonatypeRepo("releases"),
    resolvers += Resolver.sonatypeRepo("snapshots"),

    // Testing
    libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.1",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test",
    // Kiama
    libraryDependencies += "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.0.0",
    // Logger
    libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.1.7",
    libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.5.0",
    // Shapeless
    libraryDependencies += "com.chuusai" %% "shapeless" % "2.3.2",
    // Scalaz
    libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.14"
  )

/*
lazy val jsaiProject =
  ProjectRef(uri("https://github.com/nystrom/jsai.git"), "jsai")
*/

lazy val jsaiProject =
  ProjectRef(file("jsai"), "jsai")

