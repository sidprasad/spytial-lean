import Lean
import SpytialLean.Spec

namespace SpytialLean

open Lean

/-- Environment extension storing Spytial specs attached to type declarations.
    Maps declaration name → YAML string. -/
initialize spytialSpecExt : SimplePersistentEnvExtension (Name × String) (Std.HashMap Name String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (n, s) => m.insert n s) m) {}
  }

/-- Look up the Spytial spec for a declaration name, if any. -/
def getSpytialSpec? (env : Environment) (declName : Name) : Option String :=
  spytialSpecExt.getState env |>.get? declName

/-- Attach a Spytial spec (as YAML string) to a declaration name. -/
def setSpytialSpec (declName : Name) (yaml : String) : CoreM Unit :=
  modifyEnv fun env => spytialSpecExt.addEntry env (declName, yaml)

end SpytialLean
