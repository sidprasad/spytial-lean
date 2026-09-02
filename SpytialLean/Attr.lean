module

public import SpytialLean.Enum
public import Lean
public meta import SpytialLean.Spec

namespace SpytialLean

open Lean

/-! ## Spytial spec extension -/

/-- Environment extension storing Spytial specs attached to type declarations.
    Maps declaration name → structured `SpytialSpec`. -/
public meta initialize spytialSpecExt :
    SimplePersistentEnvExtension (Name × SpytialSpec) (Std.HashMap Name SpytialSpec) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (n, s) => m.insert n s) m) {}
  }

/-- Look up the Spytial spec for a declaration name, if any. -/
public meta def getSpytialSpec? (env : Environment) (declName : Name) : Option SpytialSpec :=
  spytialSpecExt.getState env |>.get? declName

/-- Attach a Spytial spec to a declaration name. -/
public meta def setSpytialSpec (declName : Name) (spec : SpytialSpec) : CoreM Unit :=
  modifyEnv fun env => spytialSpecExt.addEntry env (declName, spec)

/-! ## Named op lists -/

/-- The type of a `spytial_ops` binding. The declaration carries no data — the
    ops live in `spytialOpsExt` under its name — but being a declaration is
    what gives it a namespace, `open`, aliases and go-to-def. -/
public inductive SpytialOps where
  | mk

/-- A named op list, with the root type its ops were elaborated against.

    The ops are stored already elaborated, so a splice does not re-check them.
    Without the root, a selector naming one type's field would ride into
    another's spec and name a relation that does not exist there — silently, in
    the emitted JSON. The splice compares roots instead. -/
public meta structure RootedOps where
  root : Name
  ops : SpytialSpec

/-- Environment extension storing named op lists (`spytial_ops`).
    Maps the `SpytialOps` declaration's name → its `RootedOps`. -/
public meta initialize spytialOpsExt :
    SimplePersistentEnvExtension (Name × RootedOps) (Std.HashMap Name RootedOps) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, b) => m.insert n b
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (n, b) => m.insert n b) m) {}
  }

/-- Look up the op list bound to a declaration name, if any. -/
public meta def getSpytialOps? (env : Environment) (declName : Name) : Option RootedOps :=
  spytialOpsExt.getState env |>.get? declName

/-- Bind an op list to a declaration name. -/
public meta def setSpytialOps (declName : Name) (ops : RootedOps) : CoreM Unit :=
  modifyEnv fun env => spytialOpsExt.addEntry env (declName, ops)

/-! ## Spytial coverage opt-out extension -/

/-- Environment extension recording declarations explicitly waived from Spytial
    coverage. Maps declaration name → reason string (may be empty). -/
public meta initialize spytialOptOutExt :
    SimplePersistentEnvExtension (Name × String) (Std.HashMap Name String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (n, s) => m.insert n s) m) {}
  }

/-- Look up the opt-out reason for a declaration name, if it has been waived. -/
public meta def getSpytialOptOut? (env : Environment) (declName : Name) : Option String :=
  spytialOptOutExt.getState env |>.get? declName

/-- Explicitly waive a declaration from Spytial coverage, recording a reason. -/
public meta def setSpytialOptOut (declName : Name) (reason : String) : CoreM Unit :=
  modifyEnv fun env => spytialOptOutExt.addEntry env (declName, reason)

end SpytialLean
