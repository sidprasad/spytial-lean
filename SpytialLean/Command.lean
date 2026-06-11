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

/-- `#spytial.typespec <term>` prints the YAML spec that `lookupTypeSpec` resolves
    for the term's head type (via `spytial_spec`), or `none` if no spec applies.

    This is the spec lookup itself — the same lookup `#spytial` performs when no
    explicit `with [...]` block is given. For structures and type classes (which
    *are* structures in Lean 4) it walks the parent chain and composes specs
    root-first, so a child inherits a parent's `spytial_spec` (PLAN.md #2). Use it
    to confirm that a parent spec is found and merged for a child value — the
    YAML it prints contains the lines from every spec in the chain. -/
syntax (name := spytialTypeSpecDebug) "#spytial.typespec " term : command

@[command_elab spytialTypeSpecDebug]
def elabSpytialTypeSpecDebug : CommandElab := fun
  | `(#spytial.typespec $t:term) => do
    let result ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      lookupTypeSpec e
    match result with
    | some yaml => logInfo m!"{yaml}"
    | none      => logInfo m!"none"
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

/-! ## Proof-state tactic -/

/-- Resolve a human-readable relation name from the head of a Prop application,
    or `none` if the head is not something we name a relation after.

    - A `.const R` head yields `R`'s short name (e.g. `LT.lt` → `lt`).
    - A `.fvar` head yields the local declaration's user-facing name. This is the
      common case for proof-state goals: a relation introduced by `variable (R :
      α → α → Prop)` or a binder is a *free variable*, NOT a constant, so without
      this branch `R x y` would never become a relation. The fvar must be in the
      ambient local context (this runs inside `mvarId.withContext`).
    - Anything else (a `∀`/`→`/`∧` whose head is not an application of a named
      symbol) yields `none`, so the caller falls back to skipping / a `Goal`
      atom. -/
private def relNameOfHead? (head : Expr) : MetaM (Option String) := do
  match head with
  | .const n _ => return some (shortName n)
  | .fvar fvarId =>
    match (← getLCtx).find? fvarId with
    | some decl => return some (shortName decl.userName)
    | none      => return none
  | _ => return none

/-- Walk a Prop application `R a₁ … aₙ` (headed by a constant or a local free
    variable) as a relation tuple.

    Given an expression `ty` (a hypothesis or goal *type*), this:

    - returns `false` (decomposed nothing) unless `ty` is `Meta.isProp` and its
      head is a constant or local fvar `R` (see `relNameOfHead?` — local
      relations from `variable (R : …)` are fvars, so both are accepted);
    - filters the arguments to the non-proof, non-type *data* args (reusing the
      same `isProofArg` predicate the value walker uses);
    - if ≥ 2 data args survive, walks each as an atom via `walkExpr` and adds ONE
      tuple to a relation named `{prefix}{R}` connecting them in order, returning
      `true`;
    - if exactly 1 data arg survives, walks it as a lone atom (it appears in the
      diagram but carries no edge — a unary relation has no endpoints) and
      returns `true`;
    - if 0 data args survive, emits nothing and returns `false`.

    `pfx` is prepended to the relation name: hypotheses pass `""`, goals pass
    `"⊢ "`, so specs can style goal edges differently from hypothesis edges. The
    relation name is R's short name, NOT the hypothesis binder name — the
    relation carries the meaning, and the binder name is intentionally dropped
    for now (a deliberate simplification; see the `spytial_goals` docstring). -/
private def walkPropApp (cfg : WalkConfig) (pfx : String) (ty : Expr) :
    StateT WalkState MetaM Bool := do
  -- Only const-/fvar-headed Prop applications become relations.
  unless ← Meta.isProp ty do return false
  let some rName ← relNameOfHead? ty.getAppFn | return false
  let relName := pfx ++ rName
  -- Keep only the genuine data arguments. Drop proofs and types (as the value
  -- walker does), AND drop instance arguments: a notation-class application like
  -- `a < b` desugars to `@LT.lt Nat instLTNat a b`, and the `instLTNat` instance
  -- is `Type`-valued (not a proof or sort) so it survives `isProofArg`. Walking
  -- it would inject a spurious `LT.mk` node and make `lt` a 3-ary `[inst, a, b]`
  -- relation instead of the intended binary `a → b`.
  let args := ty.getAppArgs
  let mut dataArgs : Array Expr := #[]
  for a in args do
    if ← isProofArg a then continue
    -- Skip instances (arguments whose type is a type class).
    if (← Meta.isClass? (← Meta.inferType a)).isSome then continue
    dataArgs := dataArgs.push a
  if dataArgs.size == 0 then
    -- Nothing to anchor a relation on (e.g. `R` is a 0-ary or all-proof prop).
    return false
  -- Walk every surviving data arg into the shared diagram.
  let mut ids : Array String := #[]
  for a in dataArgs do
    let id ← walkExpr cfg a
    ids := ids.push id
  if dataArgs.size == 1 then
    -- A single data arg can't form an edge; its atom is already in the diagram.
    return true
  -- ≥ 2 data args: connect them in order with one tuple.
  let types := Array.replicate ids.size relName
  modify fun s => s.addTuple relName types { atoms := ids, types := types }
  return true

open Tactic in
/-- `spytial_goals` renders the CURRENT proof state — all goals and their local
    hypotheses — as a single spatial relational diagram in the Lean infoview.

    For each goal (and inside each goal's own context, so hypotheses resolve):

    - A hypothesis whose **type is a Prop application** `R a b …` headed by a
      named symbol — a constant (`LT.lt a b` from `a < b`) OR a *local* free
      variable (a relation from `variable (R : …)` or a binder; these are fvars,
      not constants) — becomes a tuple in a relation named after `R` (the
      hypothesis binder name, e.g. `h`, is *not* rendered — the relation name
      carries the meaning). Only the data arguments are walked as atoms; proofs,
      types, AND instance arguments (e.g. the `LT Nat` instance inside `a < b`)
      are dropped. With ≥ 2 data args they are connected by one tuple; with
      exactly 1, the lone atom appears with no edge; with 0, the hypothesis is
      skipped.
    - A **data hypothesis** (type is not a Prop, e.g. `t : Tree`) is
      relationalized through the normal walker. An abstract hypothesis variable
      (no definition) has no structure to descend into and renders as a single
      atom typed by its type's head.
    - A Prop hypothesis that is **not** a named-symbol application (e.g.
      `∀ x, P x`, `A ∧ B`, `A → B`) is skipped; a one-line `logInfo` note reports
      how many such hypotheses were skipped so they aren't silently missing.
    - Each **goal** target gets the same Prop-application treatment, but its
      relation name is prefixed `⊢ ` (so `.atomColor`/edge specs can distinguish
      goal structure from hypotheses). A goal that is not a decomposable Prop
      application becomes a single atom whose `type` field is `"Goal"` (so
      `.atomColor (selector := "Goal")` works) and whose label is the
      pretty-printed goal type.

    Everything is walked into ONE shared diagram, so a hypothesis and a goal that
    mention the same term point at the same atom.

    Use `spytial_goals with [<ops>]` to attach layout operations, just like the
    `spytial` tactic. There is no single subject type, so no `spytial_spec`
    fallback applies; without a `with` block, no spec YAML is sent.

    ```
    example {α : Type} (R : α → α → Prop) (x y : α)
        (h : R x y) (hsymm : ∀ a b, R a b → R b a) : R y x := by
      spytial_goals
      exact hsymm x y h
    ```

    The diagram shows relation `R` with the tuple `x → y` (from `h`), the goal
    relation `⊢ R` with the tuple `y → x`, and a note that `hsymm` (a `∀`) was
    skipped.

    **Experimental.** This tactic is new and its output shape may change. Stretch
    goals from the issue — tactic diff (before/after a step), dependency
    highlighting, and interactive selection — are not yet implemented. -/
syntax (name := spytialGoalsTactic) "spytial_goals" (" with " term)? : tactic

open Tactic in
@[tactic spytialGoalsTactic]
def elabSpytialGoalsTactic : Tactic := fun stx => do
  let specOpt := stx[1]
  -- Spec partitioning mirrors the other tactics: `.notationLabel` ops configure
  -- the walk (collapsed types); the rest become YAML. There is no subject type,
  -- so no type-attached spec fallback — without `with`, no YAML.
  let (cfg, yaml) ← if specOpt.isNone then
      pure ({ : WalkConfig }, none)
    else do
      let specTerm := specOpt[1]!
      let spec ← evalSpytialSpec specTerm
      pure ({ collapseTypes := spec.collapseTypes : WalkConfig },
            some (SpytialSpec.toYaml spec.withoutRelationalizerOps))

  -- `getGoals` lives in `TacticM`; snapshot the goal list here, then walk it all
  -- inside one shared `StateT WalkState MetaM` so the diagram is shared.
  let goals ← getGoals
  let walk : StateT WalkState MetaM Nat := do
    let mut skipped : Nat := 0
    for mvarId in goals do
      skipped ← mvarId.withContext do
        let mut skipped := skipped
        -- Hypotheses (skip implementation-detail decls).
        for decl in ← getLCtx do
          if decl.isImplementationDetail then continue
          let hypTy ← instantiateMVars decl.type
          if ← Meta.isProp hypTy then
            -- Prop hypothesis: relation if it is a named-symbol (const/fvar)
            -- application, else skip and count it for the note.
            let decomposed ← walkPropApp cfg "" hypTy
            unless decomposed do
              skipped := skipped + 1
          else
            -- Data hypothesis: relationalize its fvar structurally.
            let fv ← instantiateMVars decl.toExpr
            let _ ← walkExpr cfg fv
        -- Goal target.
        let goalTy ← instantiateMVars (← mvarId.getType)
        let decomposed ← walkPropApp cfg "⊢ " goalTy
        unless decomposed do
          -- Not a decomposable Prop application: a single `Goal`-typed atom.
          let label ← ppLabel goalTy
          modify fun s =>
            let (atomId, s) := s.freshId
            s.addAtom { id := atomId, type := "Goal", label := label }
        return skipped
    return skipped

  let (skipped, state) ← walk.run {}
  let di := state.toDataInstance

  if skipped > 0 then
    logInfo m!"spytial_goals: skipped {skipped} hypothesis(es) that are not \
      relation applications (e.g. `∀`, `∧`, `→`)."

  let props : Json := Json.mkObj <|
    [("dataInstance", toJson di)] ++
    match yaml with
    | some s => [("cndSpec", toJson s)]
    | none => []

  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

/-- `spytial_goals_datum` prints the JSON data instance for the current proof
    state (the debugging counterpart of `spytial_goals`, mirroring the `.datum`
    debug commands). It walks the same hypotheses and goals but `logInfo`s the
    JSON instead of opening the widget, so the structure is visible in the build
    log.

    The keyword is `spytial_goals_datum` (underscore), not `spytial_goals.datum`:
    in tactic position a trailing `.datum` lexes as a field projection rather than
    part of the keyword, so the dotted form does not parse. The `#spytial.datum`
    *command* can use a dot because `#`-prefixed command tokens are lexed whole. -/
syntax (name := spytialGoalsDatumTactic) "spytial_goals_datum" : tactic

open Tactic in
@[tactic spytialGoalsDatumTactic]
def elabSpytialGoalsDatumTactic : Tactic := fun _stx => do
  let goals ← getGoals
  let walk : StateT WalkState MetaM Unit := do
    for mvarId in goals do
      mvarId.withContext do
        for decl in ← getLCtx do
          if decl.isImplementationDetail then continue
          let hypTy ← instantiateMVars decl.type
          if ← Meta.isProp hypTy then
            let _ ← walkPropApp ({ : WalkConfig }) "" hypTy
          else
            let fv ← instantiateMVars decl.toExpr
            let _ ← walkExpr ({ : WalkConfig }) fv
        let goalTy ← instantiateMVars (← mvarId.getType)
        let decomposed ← walkPropApp ({ : WalkConfig }) "⊢ " goalTy
        unless decomposed do
          let label ← ppLabel goalTy
          modify fun s =>
            let (atomId, s) := s.freshId
            s.addAtom { id := atomId, type := "Goal", label := label }
  let (_, state) ← walk.run {}
  let json := toJson state.toDataInstance
  logInfo m!"{json.pretty}"

end SpytialLean
