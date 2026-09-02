import Lake
open Lake DSL System

package spytialLean where
  preferReleaseBuild := true
  buildArchive? := "SpytialLean.tar.gz"
  releaseRepo := "https://github.com/sidprasad/spytial-lean"

require iykyk from
  git "https://github.com/sidprasad/iykyk" @ "v0.1.2"

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
    let sgqManifest := pkg.dir / "node_modules" / "simple-graph-query" /
      "docs" / "sgq-language.json"
    let spytialManifest := pkg.widgetDir / "node_modules" / "spytial-core" /
      "docs" / "spytial-language.json"
    let depsMissing := !(← sgqManifest.pathExists) || !(← spytialManifest.pathExists)
    if depsMissing then
      pkg.runPnpmCommand #["install", "--frozen-lockfile"]
    let traceFile := pkg.buildDir / "js" / "lake.trace"
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      unless depsMissing do
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

/-! ## Files read at elaboration time

Lean's import graph sees only imports, so a file a module reads while it
elaborates (`include_str`, `IO.FS.readFile`) is invisible to the build:
editing it leaves a stale olean. Each such file is traced here and listed in
the reading library's `needs`. Both live under node_modules, which exists
only after `widgetJsAll`'s pnpm install — a plain `input_file` races it and
fails a fresh checkout's first build. Sequencing after `widgetJsAll` is
free: the library already waits on it for the JS embed. -/

target sgqManifest pkg : Unit := do
  (← widgetJsAll.fetch).mapM fun _ => do
    addTrace (← computeTrace (pkg.dir / "node_modules" / "simple-graph-query" /
      "docs" / "sgq-language.json"))

target spytialManifest pkg : Unit := do
  (← widgetJsAll.fetch).mapM fun _ => do
    addTrace (← computeTrace (pkg.widgetDir / "node_modules" / "spytial-core" /
      "docs" / "spytial-language.json"))

/-- `SpytialTests/SelectorLoweringTest.lean`'s golden. -/
input_file sgqLoweringGolden where
  path := "SpytialTests" / "SelectorLoweringTest.golden.tsv"
  text := true

@[default_target]
lean_lib SpytialLean where
  needs := #[widgetJsAll, sgqManifest, spytialManifest]

/-! Both libraries glob their directory, so a file added there is built without
    an edit here. Neither has a root module: nothing imports a demo or a test. -/

lean_lib Demos where
  globs := #[.submodules `Demos]
  needs := #[widgetJsAll]

/-- Headless unit tests: `lake build SpytialTests`. -/
lean_lib SpytialTests where
  globs := #[.submodules `SpytialTests]
  needs := #[sgqLoweringGolden]

require proofwidgets from
  git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.105"
