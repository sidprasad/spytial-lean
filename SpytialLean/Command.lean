import Lean
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.Tactic
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

/-- Try to find a Spytial spec attached to the head type of an expression.
    For structures, walks the parent chain and composes specs (parent-first). -/
private def lookupTypeSpec (e : Expr) : MetaM (Option String) := do
  let ty ← inferType e
  let tyHead := (← whnf ty).getAppFn
  match tyHead with
  | .const n _ => do
    let env ← getEnv
    if isStructure env n then
      -- Walk the structure parent chain (C3 linearization, nearest-first)
      let parents ← getAllParentStructures n
      -- Root-first order, self last
      let allNames := parents.reverse.toList ++ [n]
      let yamls := allNames.filterMap (getSpytialSpec? env ·)
      match yamls with
      | []    => return none
      | [one] => return some one
      | _     => return some (mergeSpecYamls yamls)
    else
      -- Plain inductive — direct lookup
      return getSpytialSpec? env n
  | _ => return none

@[command_elab spytialCmd]
def elabSpytialCmd : CommandElab := fun
  | stx@`(#spytial $t:term $[with $spec?]?) => do
    let (dataInstance, specYaml) ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      -- Evaluate the spec FIRST: relationalizer-side ops (`.notationLabel`) must
      -- influence the walk, so they are partitioned into `WalkConfig.collapseTypes`
      -- while the remaining (widget) ops become the YAML.
      let (cfg, yaml) ← match spec? with
        | some specTerm => do
          let spec ← evalSpytialSpec specTerm
          pure ({ collapseTypes := spec.collapseTypes : WalkConfig },
                some (SpytialSpec.toYaml spec.withoutRelationalizerOps))
        | none => do
          -- Type-attached specs are stored as YAML and cannot carry `.notationLabel`.
          pure ({ : WalkConfig }, ← lookupTypeSpec e)
      let di ← relationalize e cfg
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
      -- Type-attached specs are stored as YAML in the environment extension, so
      -- relationalizer-side ops (`.notationLabel`) cannot round-trip through them
      -- (PLAN.md #24). Rather than silently drop them, reject them clearly.
      unless spec.collapseTypes.isEmpty do
        throwError "'.notationLabel' is not supported in type-attached specs yet; \
          use it in a `with [...]` block"
      return SpytialSpec.toYaml spec
    liftCoreM <| setSpytialSpec declName yamlStr
  | stx => throwError "Unexpected syntax {stx}."

/-! ## spytial_relationalizer command -/

/-- `spytial_relationalizer <TypeName> <defName>` registers a custom relationalizer
    for a type. The def must have type `CustomRelationalizer`.

    ```
    def myRelationalizer : CustomRelationalizer := fun e walkExpr => do ...

    spytial_relationalizer MyType myRelationalizer
    ```
-/
syntax (name := spytialRelationalizerCmd) "spytial_relationalizer " ident ident : command

@[command_elab spytialRelationalizerCmd]
unsafe def elabSpytialRelationalizerCmd : CommandElab := fun
  | `(spytial_relationalizer $typeId:ident $defId:ident) => do
    let typeName := typeId.getId
    let defName := defId.getId
    let env ← getEnv
    unless env.contains typeName do
      throwError s!"unknown type '{typeName}'"
    unless env.contains defName do
      throwError s!"unknown definition '{defName}'"
    let fn ← liftTermElabM do
      Meta.evalExpr CustomRelationalizer
        (Lean.mkConst ``CustomRelationalizer) (Lean.mkConst defName)
    registerSpytialRelationalizer typeName fn
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Debugging commands -/

/-- `#spytial.spec <term> with [<ops>]` prints the generated YAML spec.
    Useful for debugging whether the spec is what you expect.

    Relationalizer-side ops (e.g. `.notationLabel`) are NOT YAML — they configure
    the walk, not the widget — so they are stripped before printing (just as the
    `#spytial` elaborator strips them before sending YAML to spytial-core). Their
    effect shows up in `#spytial.datum`/the diagram, not here. -/
syntax (name := spytialSpecDebug) "#spytial.spec " term " with " term : command

@[command_elab spytialSpecDebug]
def elabSpytialSpecDebug : CommandElab := fun
  | `(#spytial.spec $_t:term with $specTerm:term) => do
    let yamlStr ← liftTermElabM do
      let spec ← evalSpytialSpec specTerm
      return SpytialSpec.toYaml spec.withoutRelationalizerOps
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

/-! ## Proof visualization -/

/-- `#spytial.proof <term>` visualizes a proof term without filtering Prop-typed fields.
    Unlike `#spytial` (data mode), this shows the full proof structure — sub-proofs,
    premises, and witnesses are all included as nodes and edges.

    Use `with [...]` to specify layout operations.
-/
syntax (name := spytialProofCmd) "#spytial.proof " term (" with " term)? : command

@[command_elab spytialProofCmd]
def elabSpytialProofCmd : CommandElab := fun
  | stx@`(#spytial.proof $t:term $[with $spec?]?) => do
    let (dataInstance, specYaml) ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      -- Evaluate the spec first so `.notationLabel` ops can configure the walk
      -- (collapsed types) while proof mode keeps `filterProofs := false`.
      let (cfg, yaml) ← match spec? with
        | some specTerm => do
          let spec ← evalSpytialSpec specTerm
          pure ({ filterProofs := false, collapseTypes := spec.collapseTypes : WalkConfig },
                some (SpytialSpec.toYaml spec.withoutRelationalizerOps))
        | none => pure ({ filterProofs := false : WalkConfig }, ← lookupTypeSpec e)
      let di ← relationalize e cfg
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

/-- `#spytial.proof.datum <term>` prints the JSON data instance in proof mode. -/
syntax (name := spytialProofDatumDebug) "#spytial.proof.datum " term : command

@[command_elab spytialProofDatumDebug]
def elabSpytialProofDatumDebug : CommandElab := fun
  | `(#spytial.proof.datum $t:term) => do
    let dataInstance ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      relationalize e { filterProofs := false }
    let json := toJson dataInstance
    logInfo m!"{json.pretty}"
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Enumeration -/

/-- Elaborate `t` and check that it denotes a *type* (its inferred type is a
    sort). Returns the elaborated type expression. Errors clearly if the user
    passed a value instead of a type. -/
private def elabAsType (t : Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let eTy ← Meta.inferType e
  unless (← Meta.whnf eTy).isSort do
    throwError "#spytial.enumerate expects a type, but '{e}' is a value of type '{eTy}'. \
      Pass a type such as `Bool`, `Fin 5`, or a zero-arity enum inductive."
  return e

/-- Look up a Spytial spec attached to a type *by the type itself* (not by the
    type of a value). Used by `#spytial.enumerate`, whose argument is already a
    type expression. -/
private def lookupSpecForType (ty : Expr) : MetaM (Option String) := do
  match (← whnf ty).getAppFn with
  | .const n _ => return getSpytialSpec? (← getEnv) n
  | _ => return none

/-- Enumerate all inhabitants of `ty` (via `tryEnumerateDomain`) and walk them
    into a single shared `JsonDataInstance`. Throws a clear error naming the type
    if it is not enumerable. `cfg` forwards walker configuration (e.g. the
    `.notationLabel` collapse set) to `relationalizeAll`. -/
private def enumerateType (ty : Expr) (cfg : WalkConfig := {}) : MetaM JsonDataInstance := do
  match ← tryEnumerateDomain ty with
  | some elems => relationalizeAll (elems.map (·.2)) cfg
  | none =>
    throwError "#spytial.enumerate cannot enumerate '{ty}'. Enumerable types are: \
      Bool, Fin n (n ≤ 20), and inductive types whose constructors all take no arguments."

/-- `#spytial.enumerate <Type>` enumerates ALL inhabitants of a finite type and
    renders the entire population in a single spatial diagram.

    Enumerable types are `Bool`, `Fin n` (for `n ≤ 20`), and inductive types
    whose constructors all take no arguments. Every inhabitant is walked into one
    shared diagram, so references between them (e.g. a function field pointing at
    an enumerated element) unify.

    ```
    inductive Color | red | green | blue
    #spytial.enumerate Color
    #spytial.enumerate Bool
    #spytial.enumerate (Fin 5)
    ```

    Use `with [...]` to specify layout operations. If the enumerated type has an
    attached spec (via `spytial_spec`), it is used as the default.
-/
syntax (name := spytialEnumerateCmd) "#spytial.enumerate " term (" with " term)? : command

@[command_elab spytialEnumerateCmd]
def elabSpytialEnumerateCmd : CommandElab := fun
  | stx@`(#spytial.enumerate $t:term $[with $spec?]?) => do
    let (dataInstance, specYaml) ← liftTermElabM do
      let ty ← elabAsType t
      -- Evaluate the spec first so `.notationLabel` ops configure the enumeration
      -- walk (collapsed types) while the remaining ops become the YAML.
      let (cfg, yaml) ← match spec? with
        | some specTerm => do
          let spec ← evalSpytialSpec specTerm
          pure ({ collapseTypes := spec.collapseTypes : WalkConfig },
                some (SpytialSpec.toYaml spec.withoutRelationalizerOps))
        | none => pure ({ : WalkConfig }, ← lookupSpecForType ty)
      let di ← enumerateType ty cfg
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

/-- `#spytial.enumerate.datum <Type>` prints the JSON data instance produced by
    enumerating all inhabitants of a finite type. The debugging counterpart of
    `#spytial.enumerate`, mirroring `#spytial.datum`. -/
syntax (name := spytialEnumerateDatumDebug) "#spytial.enumerate.datum " term : command

@[command_elab spytialEnumerateDatumDebug]
def elabSpytialEnumerateDatumDebug : CommandElab := fun
  | `(#spytial.enumerate.datum $t:term) => do
    let dataInstance ← liftTermElabM do
      let ty ← elabAsType t
      enumerateType ty
    let json := toJson dataInstance
    logInfo m!"{json.pretty}"
  | stx => throwError "Unexpected syntax {stx}."

/-! ## spytial tactic -/

open Tactic in
/-- `spytial <term>` displays a spatial relational diagram in the Lean infoview
    during tactic mode. Hypothesis names and local bindings are in scope.

    Use `spytial <term> with [<ops>]` to specify layout operations, just like the
    `#spytial` command.

    ```
    example (t : RBTree Nat) : True := by
      spytial t
      trivial
    ```
-/
syntax (name := spytialTactic) "spytial " term (" with " term)? : tactic

open Tactic in
@[tactic spytialTactic]
def elabSpytialTactic : Tactic := fun stx => do
    let t := stx[1]
    let specOpt := stx[2]
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    -- Evaluate the spec first so `.notationLabel` ops configure the walk.
    let (cfg, yaml) ← if specOpt.isNone then
        pure ({ : WalkConfig }, ← lookupTypeSpec e)
      else do
        let specTerm := specOpt[1]!
        let spec ← evalSpytialSpec specTerm
        pure ({ collapseTypes := spec.collapseTypes : WalkConfig },
              some (SpytialSpec.toYaml spec.withoutRelationalizerOps))
    let di ← relationalize e cfg

    let props : Json := Json.mkObj <|
      [("dataInstance", toJson di)] ++
      match yaml with
      | some s => [("cndSpec", toJson s)]
      | none => []

    savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

/-! ## Proof tactic -/

open Tactic in
/-- `spytial.proof <term>` visualizes a proof term in tactic mode,
    showing the full proof structure without filtering Prop-typed fields. -/
syntax (name := spytialProofTactic) "spytial.proof " term (" with " term)? : tactic

open Tactic in
@[tactic spytialProofTactic]
def elabSpytialProofTactic : Tactic := fun stx => do
    let t := stx[1]
    let specOpt := stx[2]
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    -- Evaluate the spec first so `.notationLabel` ops configure the walk;
    -- proof mode keeps `filterProofs := false`.
    let (cfg, yaml) ← if specOpt.isNone then
        pure ({ filterProofs := false : WalkConfig }, ← lookupTypeSpec e)
      else do
        let specTerm := specOpt[1]!
        let spec ← evalSpytialSpec specTerm
        pure ({ filterProofs := false, collapseTypes := spec.collapseTypes : WalkConfig },
              some (SpytialSpec.toYaml spec.withoutRelationalizerOps))
    let di ← relationalize e cfg

    let props : Json := Json.mkObj <|
      [("dataInstance", toJson di)] ++
      match yaml with
      | some s => [("cndSpec", toJson s)]
      | none => []

    savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

end SpytialLean
