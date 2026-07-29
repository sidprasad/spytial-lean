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

def Lake.Package.runPnpmCommand (pkg : Package) (args : Array String) : LogIO Unit :=
  if Platform.isWindows then
    proc {
      cmd := "powershell"
      args := #["-Command", "pnpm.cmd"] ++ args
      cwd := some pkg.widgetDir
    } (quiet := true)
  else
    proc {
      cmd := "pnpm"
      args
      cwd := some pkg.widgetDir
    } (quiet := true)

input_file widgetPackageJson where
  path := widgetDir / "package.json"
  text := true

input_file widgetPnpmLock where
  path := widgetDir / "pnpm-lock.yaml"
  text := true

input_dir widgetJsSrcs where
  path := widgetDir / "src"
  filter := .extension <| .mem #["ts", "tsx", "js", "jsx"]
  text := true

input_file widgetRollupConfig where
  path := widgetDir / "rollup.config.js"
  text := true

input_file widgetRollupVirtual where
  path := widgetDir / "rollup.virtual.mjs"
  text := true

input_file widgetTsconfig where
  path := widgetDir / "tsconfig.json"
  text := true

target widgetJsAll pkg : Unit := do
  let srcs ← widgetJsSrcs.fetch
  let rollupConfig ← widgetRollupConfig.fetch
  let rollupVirtual ← widgetRollupVirtual.fetch
  let tsconfig ← widgetTsconfig.fetch
  let packageJson ← widgetPackageJson.fetch
  let pnpmLock ← widgetPnpmLock.fetch
  pkg.afterBuildCacheAsync do
  srcs.bindM (sync := true) fun _ =>
  rollupConfig.bindM (sync := true) fun _ =>
  rollupVirtual.bindM (sync := true) fun _ =>
  tsconfig.bindM (sync := true) fun _ =>
  packageJson.bindM (sync := true) fun _ =>
  pnpmLock.mapM fun _ => do
    let traceFile := pkg.buildDir / "js" / "lake.trace"
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      pkg.runPnpmCommand #["install", "--frozen-lockfile"]
      pkg.runPnpmCommand #["run", "build"]
    -- the job's trace is the built JS itself, so out-of-band rebuilds re-embed
    setTrace (← computeTrace (pkg.buildDir / "js" / "spytialWidget.js"))

@[default_target]
lean_lib SpytialLean where
  needs := #[widgetJsAll]

lean_lib Demos where
  srcDir := "demos"
  roots := #[`Showcase, `ProofFieldFiltering, `FunctionFields, `TypeClassInstances, `CustomRelationalizer]
  needs := #[widgetJsAll]

/-- Headless unit tests: `lake build SpytialTests`. -/
lean_lib SpytialTests where
  srcDir := "tests"
  roots := #[`TypeShapeTest, `CoverageTest, `IdentityTest]

require proofwidgets from
  git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.105"
