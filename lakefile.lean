import Lake
open Lake DSL System

package spytialLean where
  preferReleaseBuild := true
  buildArchive? := "SpytialLean.tar.gz"
  releaseRepo := "https://github.com/sidprasad/spytial-lean"
  -- The include_str'd widget bundle is minified JS; silence the cosmetic C
  -- warnings its size and stray bidi chars trigger when Widget.c is compiled
  -- (no effect on the infoview, which reads the string from oleans, not C).
  moreLeancArgs := #["-Wno-bidi-chars", "-Wno-overlength-strings"]

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

/-! ## Render-test harness (tests/render/) -/

input_file renderEntry where
  path := "tests" / "render" / "entry.mjs"
  text := true

input_file renderRollupConfig where
  path := "tests" / "render" / "rollup.config.mjs"
  text := true

/-- Self-contained browser bundle for the headless render tests: the real
    widget component + react + the spytial-core virtual modules. Built into
    `tests/render/dist/harness.js`; consumed by `tests/render/render.spec.mjs`. -/
target renderHarnessJs pkg : Unit := do
  let widgetJs ← widgetJsAll.fetch
  let entry ← renderEntry.fetch
  let cfg ← renderRollupConfig.fetch
  let virt ← widgetRollupVirtual.fetch
  widgetJs.bindM (sync := true) fun _ =>
  entry.bindM (sync := true) fun _ =>
  cfg.bindM (sync := true) fun _ =>
  virt.mapM fun _ => do
    let traceFile := pkg.buildDir / "renderHarness.trace"
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      pkg.runPnpmCommand #["run", "build:render-harness"]

@[default_target]
lean_lib SpytialLean where
  needs := #[widgetJsAll]

lean_lib Demos where
  srcDir := "demos"
  roots := #[`Showcase, `ProofFieldFiltering, `FunctionFields, `TypeClassInstances,
             `CustomRelationalizer, `HoareLogic, `OperationalSemantics, `ProofTerms,
             `PartialTerms, `BDD]
  needs := #[widgetJsAll]

/-- Headless unit tests: `lake build SpytialTests`. -/
lean_lib SpytialTests where
  srcDir := "tests"
  roots := #[`TypeShapeTest, `CoverageTest, `SelectorTest, `IdentityTest,
             `IdentityWalkTest]

require proofwidgets from
  git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.105"
