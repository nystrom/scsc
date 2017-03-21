scalaVersion := "2.12.0"

name := "scsc"

organization := "ch.usi.scsc"

version := "0.1"

sbtRatsSettings

ratsScalaRepetitionType := Some (ListType)

ratsUseScalaOptions := true

ratsUseScalaPositions := true

ratsUseKiama := 2

ratsDefineASTClasses := true

ratsDefinePrettyPrinter := true

ratsUseDefaultSpacing := true

ratsUseDefaultLayout := true

ratsUseDefaultComments := true

ratsUseDefaultWords := true

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"
libraryDependencies += "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.0.0"
// Logger
libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.1.7"
libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.5.0"
