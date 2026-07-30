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

/-! ## JS build targets

The repo is one pnpm workspace: `widget/` bundles the infoview component and
`tests/render/` bundles the headless render harness, with every shared version
pinned once in the root `pnpm-workspace.yaml` catalog. pnpm therefore always
runs from the package root — the workspace root, where the single lockfile
lives — and `-C` picks the member to act on. `--filter` would read better but
exits 0 when no package matches its name, so a renamed member would silently
build nothing. -/

def widgetDir : FilePath := "widget"
def renderDir : FilePath := "tests" / "render"

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

/-! ## Render-test harness (tests/render/) -/

input_file renderEntry where
  path := renderDir / "entry.mjs"
  text := true

input_file renderRollupConfig where
  path := renderDir / "rollup.config.mjs"
  text := true

/-- Self-contained browser bundle for the headless render tests: the real
    widget component + react + the spytial-core virtual modules. Built into
    `tests/render/dist/harness.js`; consumed by `tests/render/render.spec.mjs`. -/
target renderHarnessJs pkg : Unit := do
  let inputs := (← widgetJsAll.fetch)
    |>.mix (← fetchPnpmWorkspaceFiles)
    |>.mix (← renderEntry.fetch)
    |>.mix (← renderRollupConfig.fetch)
    |>.mix (← widgetRollupVirtual.fetch)
  inputs.mapM fun _ => do
    -- `entry.mjs` imports `widget/dist/spytialWidget.js`, the *tsc* output,
    -- while `widgetJsAll` traces the *rollup* output under `.lake`. Depending
    -- on that target is what gets the file written (one `pnpm run build`
    -- produces both), but only mixing its trace in here makes the harness
    -- rebuild when the component changes.
    addTrace (← computeTrace (pkg.widgetDir / "dist" / "spytialWidget.js"))
    let harnessJs := pkg.renderDir / "dist" / "harness.js"
    buildUnlessUpToDate harnessJs (← getTrace) (pkg.buildDir / "renderHarness.trace") do
      pkg.runPnpmCommand #["-C", renderDir.toString, "run", "build:render-harness"]

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
  roots := #[`TypeShapeTest, `CoverageTest, `TacticTest, `SelectorTest,
             `IdentityTest, `IdentityWalkTest]

require proofwidgets from
  git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.105"
