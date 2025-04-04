// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

ThisBuild / scalaVersion := "2.13.10"
ThisBuild / scalacOptions ++= Seq(
    "-encoding", "UTF-8",               // Enforce UTF-8, instead of relying on properly set locales
    "-deprecation",                     // Warn when using deprecated language features
    "-unchecked",                       // Warn on generated code assumptions
    "-feature",                         // Warn on features that requires explicit import
    "-Wunused",                         // Warn on unused imports
    "-Ypatmat-exhaust-depth", "40",     // Increase depth of pattern matching analysis
)

// Enforce UTF-8, instead of relying on properly set locales
ThisBuild / javacOptions ++= Seq("-encoding", "UTF-8", "-charset", "UTF-8", "-docencoding", "UTF-8")
ThisBuild / javaOptions  ++= Seq("-Dfile.encoding=UTF-8")

// Publishing settings

// Allows 'publishLocal' SBT command to include test artifacts in a dedicated JAR file
// (whose name is postfixed by 'test-source') and publish it in the local Ivy repository.
// This JAR file contains all classes and resources for testing and projects like Carbon
// and Silicon can rely on it to access the test suit implemented in Silver.
ThisBuild / Test / publishArtifact := true

// Import general settings from Silver
lazy val silver = project in file("silver")

// specific project settings
lazy val silver_sif_extension = (project in file("."))
  .dependsOn(silver % "compile->compile;test->test")
  .settings(

    // General settings
    name := "silver-sif-extension",
    organization := "viper",
    version := "1.1-SNAPSHOT",

    // Compilation settings
    //libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.0",
    //libraryDependencies += "org.apache.commons" % "commons-pool2" % "2.6.0",

    // Run settings
    run / javaOptions += "-Xss128m",

    // Test settings
    Test / javaOptions ++= (run / javaOptions).value,
    // Options passed to JVMs forked by test-related Sbt command.
    // See http://www.scala-sbt.org/0.12.4/docs/Detailed-Topics/Forking.html
    // In contrast to what the documentation states, it seemed
    // that neither were the options passed to Sbt's JVM forwarded
    // to forked JVMs, nor did "javaOptions in (Test,run)"
    // work for me (Malte, using Sbt 0.12.4).
    // You can inspect the settings in effect using via
    // "show javaOptions" on the Sbt console.

    fork := true,
    // Fork Silicon when run and tested. Avoids problems with file
    // handlers on Windows 7 that remain open until Sbt is closed,
    // which makes it very annoying to work on test files.
    // There have been reports about problems with forking. If you
    // experience strange problems, disable forking and try again.
    // Malte 2013-11-18: Jenkins failed with
    // "OutOfMemoryError: unable to create new native thread".
    // Reducing the stack size from 256M to 128M seems to resolve
    // the problem and Silicon seems to be fine with less stack.
    // Not sure what to do if Silicon really required so much
    // stack at some point.

    // Assembly settings
    assembly / assemblyJarName := "silver-sif-extension.jar",
    assembly / test := {},
  )