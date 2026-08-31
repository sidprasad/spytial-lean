module

public import SpytialLean.Enum
public import Lean
public meta import SpytialLean.Spec

namespace SpytialLean

open Lean

public meta initialize spytialSpecExt :
    SimplePersistentEnvExtension (Name × SpytialSpec) (Std.HashMap Name SpytialSpec) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (n, s) => m.insert n s) m) {}
  }

public meta def getSpytialSpec? (env : Environment) (declName : Name) : Option SpytialSpec :=
  spytialSpecExt.getState env |>.get? declName

public meta def setSpytialSpec (declName : Name) (spec : SpytialSpec) : CoreM Unit :=
  modifyEnv fun env => spytialSpecExt.addEntry env (declName, spec)

/-! ## Named op lists -/

/-- Carries no data — the ops live in `spytialOpsExt` under its name — but
    being a declaration is what gives it a namespace, `open`, aliases and
    go-to-def. -/
public inductive SpytialOps where
  | mk

/-- Without the root, a selector naming one type's field would ride into
    another's spec and name a relation that does not exist there, silently, in
    the emitted JSON. The splice compares roots instead. -/
public meta structure RootedOps where
  root : Name
  ops : SpytialSpec

public meta initialize spytialOpsExt :
    SimplePersistentEnvExtension (Name × RootedOps) (Std.HashMap Name RootedOps) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, b) => m.insert n b
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (n, b) => m.insert n b) m) {}
  }

public meta def getSpytialOps? (env : Environment) (declName : Name) : Option RootedOps :=
  spytialOpsExt.getState env |>.get? declName

public meta def setSpytialOps (declName : Name) (ops : RootedOps) : CoreM Unit :=
  modifyEnv fun env => spytialOpsExt.addEntry env (declName, ops)

public meta initialize spytialOptOutExt :
    SimplePersistentEnvExtension (Name × String) (Std.HashMap Name String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (n, s) => m.insert n s) m) {}
  }

public meta def getSpytialOptOut? (env : Environment) (declName : Name) : Option String :=
  spytialOptOutExt.getState env |>.get? declName

public meta def setSpytialOptOut (declName : Name) (reason : String) : CoreM Unit :=
  modifyEnv fun env => spytialOptOutExt.addEntry env (declName, reason)

end SpytialLean
