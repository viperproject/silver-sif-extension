import sbt._
import Keys._
import sbtassembly.AssemblyPlugin.autoImport._
import de.oakgrove.SbtBrand.{BrandKeys, brandSettings, Val}
import de.oakgrove.SbtHgId.{HgIdKeys, hgIdSettings}
import com.typesafe.sbt.packager.archetypes.JavaAppPackaging

object SIFBuild extends Build {

  /* Base settings */

  lazy val baseSettings = (
       hgIdSettings
    ++ brandSettings
    ++ Seq(
          organization := "viper",
          version := "1.0-SNAPSHOT",
          scalaVersion := "2.11.8",
          scalacOptions in Compile ++= Seq(
            "-deprecation",
            "-unchecked",
            "-feature"
            /*"-Xfatal-warnings"*/),
          resolvers += "Sonatype OSS Snapshots" at "http://oss.sonatype.org/content/repositories/snapshots/",
          traceLevel := 10,
          maxErrors := 6))

  /* Projects */

  lazy val silver_sif_extension = {
    var p = Project(
      id = "silver-sif-extension",
      base = file("."),
      settings = (
           baseSettings
        ++ Seq(
              name := "silver-sif-extension",
              mainClass in Compile := None,
              mainClass in assembly := None,
              jarName in assembly := "silver-sif-extension.jar",
              test in assembly := {},
              fork := true,
               javaOptions in run ++= Seq("-Xss128M", "-Dfile.encoding=UTF-8"),
               javaOptions in Test += "-Xss128M",
               testOptions in Test += Tests.Argument("-oGK"),
     
              publishArtifact in Test := true,
              libraryDependencies ++= externalDep,
              BrandKeys.dataPackage := "viper.silver.sif",
              BrandKeys.dataObject := "brandingData",
              BrandKeys.data += Val("buildDate", new java.text.SimpleDateFormat("yyyy/MM/dd HH:mm:ss").format(new java.util.Date)),
              BrandKeys.data <+= scalaVersion(Val("scalaVersion", _)),
              BrandKeys.data <+= sbtBinaryVersion(Val("sbtBinaryVersion", _)),
              BrandKeys.data <+= sbtVersion(Val("sbtVersion", _)),
              BrandKeys.data <+= name(Val("sbtProjectName", _)),
              BrandKeys.data <+= version(Val("sbtProjectVersion", _)),
              BrandKeys.data <++= HgIdKeys.projectId(idOrException => {
                val id =
                  idOrException.fold(Predef.identity,
                                     _ => de.oakgrove.SbtHgId.Id("<unknown>", "<unknown>", "<unknown>", "<unknown>"))

                Seq(Val("hgid_version", id.version),
                    Val("hgid_id", id.id),
                    Val("hgid_branch", id.branch),
                    Val("hgid_tags", id.tags))
              }),
              sourceGenerators in Compile <+= BrandKeys.generateDataFile)
        ++ addCommandAlias("tn", "test-only -- -n "))
    )

    for (dep <- internalDep) {
      p = p.dependsOn(dep)
    }

    p.enablePlugins(JavaAppPackaging)
  }

  /* On the build-server, we cannot have all project in the same directory, and
   * thus we use the publish-local mechanism for dependencies.
   */

  def isBuildServer = sys.env.contains("BUILD_TAG") /* Should only be defined on the build server */

  def internalDep = if (isBuildServer) Nil else Seq(
    dependencies.silSrc % "compile->compile;test->test"
  )

  def externalDep = (
    (if (isBuildServer) Seq(dependencies.sil % "compile->compile;test->test") else Nil))

  /* Dependencies */

  object dependencies {
    lazy val sil = "viper" %% "silver" %  "0.1-SNAPSHOT"
    lazy val silSrc = RootProject(new java.io.File("../silver"))
  }
}


