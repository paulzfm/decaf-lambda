name := "decaf-in-scala"

version := "0.1"

scalaVersion := "2.13.1"

// https://mvnrepository.com/artifact/org.scala-lang/scala-reflect
libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.13.1"

// https://mvnrepository.com/artifact/org.ow2.asm/asm
libraryDependencies += "org.ow2.asm" % "asm" % "7.2-beta"

libraryDependencies += "com.github.scopt" %% "scopt" % "4.0.0-RC2"

// https://mvnrepository.com/artifact/org.apache.commons/commons-lang3
libraryDependencies += "org.apache.commons" % "commons-lang3" % "3.9"

// antlr4

enablePlugins(Antlr4Plugin)

antlr4PackageName in Antlr4 := Some("decaf.frontend.parsing.antlr")

antlr4GenListener in Antlr4 := false // default: true

antlr4GenVisitor in Antlr4 := true // default: false

// assembly

assemblyOutputPath in assembly := file("target/decaf.jar")
