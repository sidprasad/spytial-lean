import Lake
open Lake DSL System

package spytialLean where
  preferReleaseBuild := true
  buildArchive? := "SpytialLean.tar.gz"
  releaseRepo := "https://github.com/sidprasad/spytial-lean"

/-! ## Widget JS build targets -/

def widgetDir : FilePath := "widget"

nonrec def Lake.Package.widgetDir (pkg : Package) : FilePath :=
  pkg.dir / widgetDir

def Lake.Package.runNpmCommand (pkg : Package) (args : Array String) : LogIO Unit :=
  if Platform.isWindows then
    proc {
      cmd := "powershell"
      args := #["-Command", "npm.cmd"] ++ args
      cwd := some pkg.widgetDir
    } (quiet := true)
  else
    proc {
      cmd := "npm"
      args
      cwd := some pkg.widgetDir
    } (quiet := true)

input_file widgetPackageJson where
  path := widgetDir / "package.json"
  text := true

target widgetPackageLock pkg : FilePath := do
  let packageFile ← widgetPackageJson.fetch
  let packageLockFile := pkg.widgetDir / "package-lock.json"
  buildFileAfterDep (text := true) packageLockFile packageFile fun _srcFile => do
    pkg.runNpmCommand #["install"]

input_dir widgetJsSrcs where
  path := widgetDir / "src"
  filter := .extension <| .mem #["ts", "tsx", "js", "jsx"]
  text := true

input_file widgetRollupConfig where
  path := widgetDir / "rollup.config.js"
  text := true

input_file widgetTsconfig where
  path := widgetDir / "tsconfig.json"
  text := true

target widgetJsAll pkg : Unit := do
  let srcs ← widgetJsSrcs.fetch
  let rollupConfig ← widgetRollupConfig.fetch
  let tsconfig ← widgetTsconfig.fetch
  let widgetPackageLock ← widgetPackageLock.fetch
  pkg.afterBuildCacheAsync do
  srcs.bindM (sync := true) fun _ =>
  rollupConfig.bindM (sync := true) fun _ =>
  tsconfig.bindM (sync := true) fun _ =>
  widgetPackageLock.mapM fun _ => do
    let traceFile := pkg.buildDir / "js" / "lake.trace"
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      pkg.runNpmCommand #["clean-install"]
      pkg.runNpmCommand #["run", "build"]

@[default_target]
lean_lib SpytialLean where
  needs := #[widgetJsAll]

lean_lib Demos where
  srcDir := "demos"
  roots := #[`Showcase, `ProofFieldFiltering, `FunctionFields, `TypeClassInstances, `CustomRelationalizer]
  needs := #[widgetJsAll]

require proofwidgets from
  git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.75"
