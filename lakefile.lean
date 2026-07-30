import Lake
open Lake DSL System

package spytialLean where
  preferReleaseBuild := true
  buildArchive? := "SpytialLean.tar.gz"
  releaseRepo := "https://github.com/sidprasad/spytial-lean"

/-! ## JS build targets

The repo is one pnpm workspace whose sole member, `widget/`, bundles the
infoview component, with every shared version pinned once in the root
`pnpm-workspace.yaml` catalog. pnpm therefore always runs from the package
root — the workspace root, where the single lockfile lives — and `-C` picks the
member to act on. `--filter` would read better but exits 0 when no package
matches its name, so a renamed member would silently build nothing. -/

def widgetDir : FilePath := "widget"

nonrec def Lake.Package.widgetDir (pkg : Package) : FilePath :=
  pkg.dir / widgetDir

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

/-- Everything `pnpm install --frozen-lockfile` reads: the workspace layout and
    catalog, the one lockfile, and every member manifest. -/
def fetchPnpmWorkspaceFiles : FetchM (Job Unit) := do
  return Job.mixArray (traceCaption := "pnpm workspace") #[
    ← pnpmWorkspaceYaml.fetch, ← pnpmLock.fetch, ← rootPackageJson.fetch,
    ← widgetPackageJson.fetch]

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

@[default_target]
lean_lib SpytialLean where
  needs := #[widgetJsAll]

lean_lib Demos where
  srcDir := "demos"
  roots := #[`Showcase, `ProofFieldFiltering, `FunctionFields, `TypeClassInstances,
             `CustomRelationalizer, `ProofTerms, `HoareLogic, `OperationalSemantics]
  needs := #[widgetJsAll]

/-- Headless unit tests: `lake build SpytialTests`. -/
lean_lib SpytialTests where
  srcDir := "tests"
  roots := #[`TypeShapeTest, `CoverageTest, `TacticTest]

require proofwidgets from
  git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.105"
