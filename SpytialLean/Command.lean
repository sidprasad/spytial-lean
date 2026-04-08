import Lean
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Widget.UserWidget
import SpytialLean.Types
import SpytialLean.Spec
import SpytialLean.Relationalizer
import SpytialLean.Widget
import SpytialLean.Attr

namespace SpytialLean

open Lean Elab Command Term Meta Widget

/-! ## Evaluating SpytialSpec from syntax -/

/-- Evaluate a `SpytialSpec` term to a value at elaboration time. -/
private unsafe def evalSpytialSpecUnsafe (stx : Syntax) : TermElabM SpytialSpec := do
  let e ← Term.elabTerm stx (some (mkConst ``SpytialSpec))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  evalExpr SpytialSpec (mkConst ``SpytialSpec) e

@[implemented_by evalSpytialSpecUnsafe]
private opaque evalSpytialSpec (stx : Syntax) : TermElabM SpytialSpec

/-! ## #spytial command -/

/-- `#spytial <term>` displays a spatial relational diagram in the Lean infoview.

    Use `#spytial <term> with [<ops>]` to specify typed Spytial layout operations:
    ```
    #spytial myTree with [
      .orientation (selector := "left") (directions := [.left, .below]),
      .atomColor (selector := "leaf") (value := "#0066ff")
    ]
    ```

    If the type has an attached spec (via `spytial_spec`), it is used as the
    default. An explicit `with [...]` overrides it.
-/
syntax (name := spytialCmd) "#spytial " term (" with " term)? : command

/-- Try to find a Spytial spec attached to the head type of an expression. -/
private def lookupTypeSpec (e : Expr) : MetaM (Option String) := do
  let ty ← inferType e
  let tyHead := (← whnf ty).getAppFn
  match tyHead with
  | .const n _ => return getSpytialSpec? (← getEnv) n
  | _ => return none

@[command_elab spytialCmd]
def elabSpytialCmd : CommandElab := fun
  | stx@`(#spytial $t:term $[with $spec?]?) => do
    let (dataInstance, specYaml) ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let di ← relationalize e
      -- Determine spec: explicit `with [...]` > type attribute > none
      let yaml ← match spec? with
        | some specTerm => do
          let spec ← evalSpytialSpec specTerm
          pure (some (SpytialSpec.toYaml spec))
        | none => lookupTypeSpec e
      return (di, yaml)

    let props : Json := Json.mkObj <|
      [("dataInstance", toJson dataInstance)] ++
      match specYaml with
      | some s => [("cndSpec", toJson s)]
      | none => []

    liftCoreM <| savePanelWidgetInfo
      SpytialWidget.javascriptHash
      (return props)
      stx

  | stx => throwError "Unexpected syntax {stx}."

/-! ## spytial_spec command -/

/-- `spytial_spec <name> [<ops>]` attaches a Spytial layout spec to a type declaration.
    The spec is used as the default when visualizing values of that type.

    ```
    spytial_spec Tree [
      .orientation (selector := "node_0") (directions := [.left, .below]),
      .hideAtom (selector := "Nat")
    ]
    ```
-/
syntax (name := spytialSpecCmd) "spytial_spec " ident term : command

@[command_elab spytialSpecCmd]
def elabSpytialSpecCmd : CommandElab := fun
  | `(spytial_spec $id:ident $specTerm:term) => do
    let declName := id.getId
    let env ← getEnv
    unless env.contains declName do
      throwError s!"unknown declaration '{declName}'"
    let yamlStr ← liftTermElabM do
      let spec ← evalSpytialSpec specTerm
      return SpytialSpec.toYaml spec
    liftCoreM <| setSpytialSpec declName yamlStr
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Debugging commands -/

/-- `#spytial.spec <term> with [<ops>]` prints the generated YAML spec.
    Useful for debugging whether the spec is what you expect. -/
syntax (name := spytialSpecDebug) "#spytial.spec " term " with " term : command

@[command_elab spytialSpecDebug]
def elabSpytialSpecDebug : CommandElab := fun
  | `(#spytial.spec $_t:term with $specTerm:term) => do
    let yamlStr ← liftTermElabM do
      let spec ← evalSpytialSpec specTerm
      return SpytialSpec.toYaml spec
    logInfo m!"{yamlStr}"
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.datum <term>` prints the generated JSON data instance.
    Shows what atoms and relations the relationalizer produces. -/
syntax (name := spytialDatumDebug) "#spytial.datum " term : command

@[command_elab spytialDatumDebug]
def elabSpytialDatumDebug : CommandElab := fun
  | `(#spytial.datum $t:term) => do
    let dataInstance ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      relationalize e
    let json := toJson dataInstance
    logInfo m!"{json.pretty}"
  | stx => throwError "Unexpected syntax {stx}."

end SpytialLean
