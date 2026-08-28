import Lake
open Lake DSL System

package spytialLean where
  preferReleaseBuild := true
  buildArchive? := "SpytialLean.tar.gz"
  releaseRepo := "https://github.com/sidprasad/spytial-lean"

/-! ## JS build targets

pnpm runs from the workspace root and `-C` picks the member; `--filter` exits 0
when no package matches, so a rename would silently build nothing. -/

def widgetDir : FilePath := "widget"
def renderDir : FilePath := "render"

nonrec def Lake.Package.widgetDir (pkg : Package) : FilePath :=
  pkg.dir / widgetDir

nonrec def Lake.Package.renderDir (pkg : Package) : FilePath :=
  pkg.dir / renderDir

def Lake.Package.runPnpmCommand (pkg : Package) (args : Array String) : LogIO Unit :=
  if Platform.isWindows then
    proc {
      cmd := "powershell"
      args := #["-Command", "pnpm.cmd"] ++ args
      cwd := some pkg.dir
    } (quiet := true)
  else
    proc {
      cmd := "pnpm"
      args
      cwd := some pkg.dir
    } (quiet := true)

input_file pnpmWorkspaceYaml where
  path := "pnpm-workspace.yaml"
  text := true

input_file pnpmLock where
  path := "pnpm-lock.yaml"
  text := true

input_file rootPackageJson where
  path := "package.json"
  text := true

input_file widgetPackageJson where
  path := widgetDir / "package.json"
  text := true

input_file renderPackageJson where
  path := renderDir / "package.json"
  text := true

/-- Everything `pnpm install --frozen-lockfile` reads: the workspace layout and
    catalog, the one lockfile, and every member manifest. -/
def fetchPnpmWorkspaceFiles : FetchM (Job Unit) := do
  return Job.mixArray (traceCaption := "pnpm workspace") #[
    ← pnpmWorkspaceYaml.fetch, ← pnpmLock.fetch, ← rootPackageJson.fetch,
    ← widgetPackageJson.fetch, ← renderPackageJson.fetch]

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
  let inputs := (← fetchPnpmWorkspaceFiles)
    |>.mix (← widgetJsSrcs.fetch)
    |>.mix (← widgetRollupConfig.fetch)
    |>.mix (← widgetRollupVirtual.fetch)
    |>.mix (← widgetTsconfig.fetch)
  pkg.afterBuildCacheAsync do
  inputs.mapM fun _ => do
    let traceFile := pkg.buildDir / "js" / "lake.trace"
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      pkg.runPnpmCommand #["install", "--frozen-lockfile"]
      pkg.runPnpmCommand #["-C", widgetDir.toString, "run", "build"]
    -- the job's trace is the built JS itself, so out-of-band rebuilds re-embed
    setTrace (← computeTrace (pkg.buildDir / "js" / "spytialWidget.js"))

/-! ## Render harness (render/) -/

input_file renderEntry where
  path := renderDir / "entry.mjs"
  text := true

input_file renderRollupConfig where
  path := renderDir / "rollup.config.mjs"
  text := true

/-- Browser bundle for snapshot renders: widget component + react + the
    spytial-core virtual modules, into `render/dist/harness.js`. -/
target renderHarnessJs pkg : Unit := do
  let inputs := (← widgetJsAll.fetch)
    |>.mix (← fetchPnpmWorkspaceFiles)
    |>.mix (← renderEntry.fetch)
    |>.mix (← renderRollupConfig.fetch)
    |>.mix (← widgetRollupVirtual.fetch)
  inputs.mapM fun _ => do
    -- widgetJsAll traces the rollup output; entry.mjs imports the tsc one, so
    -- only this trace rebuilds the harness when the component changes.
    addTrace (← computeTrace (pkg.widgetDir / "dist" / "spytialWidget.js"))
    let harnessJs := pkg.renderDir / "dist" / "harness.js"
    buildUnlessUpToDate harnessJs (← getTrace) (pkg.buildDir / "renderHarness.trace") do
      pkg.runPnpmCommand #["-C", renderDir.toString, "run", "build:render-harness"]

/-! ## Language manifests

`SpytialLean.Sgq` and `SpytialLean.SpecLang` read these with `include_str` as
they elaborate, which Lean's import graph does not see. Naming them here is
what re-elaborates those modules when a dependency bump moves a manifest. -/

input_file sgqManifest where
  path := "node_modules" / "simple-graph-query" / "docs" / "sgq-language.json"

input_file spytialManifest where
  path := widgetDir / "node_modules" / "spytial-core" / "docs" / "spytial-language.json"

@[default_target]
lean_lib SpytialLean where
  needs := #[widgetJsAll, sgqManifest, spytialManifest]

lean_lib Demos where
  srcDir := "demos"
  roots := #[`Showcase, `ProofFieldFiltering, `FunctionFields, `TypeClassInstances,
             `CustomRelationalizer, `ProofTerms, `HoareLogic, `OperationalSemantics,
             `PartialTerms, `BDD, `Automata, `LeanSelectors]
  needs := #[widgetJsAll]

/-- `SelectorLoweringTest` reads this with `IO.FS.readFile` as it elaborates,
    which Lean's import graph does not see. Without naming it here, editing the
    golden leaves a stale olean and the comparison does not re-run. -/
input_file sgqLoweringGolden where
  path := "tests" / "SelectorLoweringTest.golden.tsv"
  text := true

/-- Headless unit tests: `lake build SpytialTests`. -/
lean_lib SpytialTests where
  srcDir := "tests"
  roots := #[`WalkCanon, `TypeShapeTest, `CoverageTest, `TacticTest, `SelectorTest,
             `LeanSelectorTest, `SelectorLoweringTest, `SgqCoverageTest,
             `SpecSurfaceTest, `IdentityTest, `IdentityWalkTest, `RelationShapeTest]
  needs := #[sgqLoweringGolden]

require proofwidgets from
  git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.105"
