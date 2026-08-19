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

/-! ## Spytial op-bundle extension -/

/-- Environment extension storing named op bundles (`spytial_ops`).
    Maps bundle name → structured `SpytialSpec`. -/
public meta initialize spytialBundleExt :
    SimplePersistentEnvExtension (Name × SpytialSpec) (Std.HashMap Name SpytialSpec) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (n, s) => m.insert n s) m) {}
  }

/-- Look up the op bundle bound to `name`, if any. -/
public meta def getSpytialBundle? (env : Environment) (name : Name) : Option SpytialSpec :=
  spytialBundleExt.getState env |>.get? name

/-- Every bound bundle name, for error messages. -/
public meta def spytialBundleNames (env : Environment) : List Name :=
  spytialBundleExt.getState env |>.keys

/-- Bind an op bundle to `name`. -/
public meta def setSpytialBundle (name : Name) (spec : SpytialSpec) : CoreM Unit :=
  modifyEnv fun env => spytialBundleExt.addEntry env (name, spec)

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
