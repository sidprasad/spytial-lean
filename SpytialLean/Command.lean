module

public import Lean
public import Lean.Elab.Command
public import Lean.Elab.Term
public import Lean.Elab.Tactic
public import Lean.Widget.UserWidget
public meta import SpytialLean.Types
public meta import SpytialLean.Spec
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.Widget
public meta import SpytialLean.Attr

namespace SpytialLean

open Lean Elab Command Term Meta Widget

public section

/-! ## Evaluating SpytialSpec from syntax -/

/-- Evaluate a `SpytialSpec` term to a value at elaboration time. -/
private meta unsafe def evalSpytialSpecUnsafe (stx : Syntax) : TermElabM SpytialSpec := do
  let e ← Term.elabTerm stx (some (mkConst ``SpytialSpec))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  evalExpr SpytialSpec (mkConst ``SpytialSpec) e

@[implemented_by evalSpytialSpecUnsafe]
private meta opaque evalSpytialSpec (stx : Syntax) : TermElabM SpytialSpec

/-! ## Widget payload

The commands and tactics below differ only in whether Prop-typed fields are
filtered; `spytialPayloadProps` is the single place that decides what the widget
receives. -/

/-- Try to find a Spytial spec attached to the head type of an expression.
    For structures, walks the parent chain and composes specs (parent-first). -/
private meta def lookupTypeSpec (e : Expr) : MetaM (Option SpytialSpec) := do
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
      let specs := allNames.filterMap (getSpytialSpec? env ·)
      return if specs.isEmpty then none else some specs.flatten
    else
      -- Plain inductive — direct lookup
      return getSpytialSpec? env n
  | _ => return none

/-- Elaborate a term to a fully instantiated expression and relationalize it. -/
private meta def elabRelationalized (t : Syntax) (cfg : WalkConfig := {}) :
    TermElabM (Expr × JsonDataInstance) := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  return (e, ← relationalize e cfg)

/-- Elaborate a term and resolve its layout spec: an explicit `with <ops>`
    overrides a spec attached to the term's type. The composed spec is rendered
    to YAML once here, at payload-build time. -/
private meta def elabSpytialPayload (t : Syntax) (spec? : Option Syntax)
    (cfg : WalkConfig) : TermElabM (JsonDataInstance × Option String) := do
  let (e, di) ← elabRelationalized t cfg
  let spec ← match spec? with
    | some specTerm => some <$> evalSpytialSpec specTerm
    | none => lookupTypeSpec e
  return (di, spec.map SpytialSpec.toYaml)

private meta def spytialProps (di : JsonDataInstance) (cndSpec? : Option String) : Json :=
  Json.mkObj <|
    [("dataInstance", toJson di)] ++
    match cndSpec? with
    | some s => [("cndSpec", toJson s)]
    -- absent, not null: the widget reads a missing `cndSpec` as free layout
    | none => []

/-- The payload `#spytial` hands the infoview. Public so out-of-tree frontends
    (the render tests, document backends) render what the infoview does rather
    than reassembling it. -/
public meta def spytialPayloadProps (t : Syntax) (spec? : Option Syntax := none)
    (cfg : WalkConfig := {}) : TermElabM Json := do
  let (di, cndSpec?) ← elabSpytialPayload t spec? cfg
  return spytialProps di cndSpec?

/-- The `with <ops>` term of an optional trailing `with` clause in `stx`. -/
private meta def withClauseSpec? (stx : Syntax) : Option Syntax :=
  if stx.isNone then none else some stx[1]

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

@[command_elab spytialCmd]
meta def elabSpytialCmd : CommandElab := fun
  | stx@`(#spytial $t:term $[with $spec?]?) => do
    let props ← liftTermElabM <| spytialPayloadProps t (spec?.map (·.raw))
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
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
meta def elabSpytialSpecCmd : CommandElab := fun
  | `(spytial_spec $id:ident $specTerm:term) => do
    let declName ← resolveGlobalConstNoOverload id
    let spec ← liftTermElabM <| evalSpytialSpec specTerm
    liftCoreM <| setSpytialSpec declName spec
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
meta def elabSpytialRelationalizerCmd : CommandElab := fun
  | `(spytial_relationalizer $typeId:ident $defId:ident) => do
    let typeName ← resolveGlobalConstNoOverload typeId
    let defName ← resolveGlobalConstNoOverload defId
    -- fail mistyped registrations here, not opaquely at dispatch
    liftTermElabM do
      let declType := (← getConstInfo defName).type
      unless (← Meta.isDefEq declType (Lean.mkConst ``CustomRelationalizer)) do
        throwError s!"'{defName}' must have type `CustomRelationalizer`"
    liftCoreM <| setSpytialRelationalizer typeName defName
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Debugging commands -/

/-- `#spytial.spec <term> with [<ops>]` prints the generated YAML spec.
    Useful for debugging whether the spec is what you expect. -/
syntax (name := spytialSpecDebug) "#spytial.spec " term " with " term : command

@[command_elab spytialSpecDebug]
meta def elabSpytialSpecDebug : CommandElab := fun
  | `(#spytial.spec $_t:term with $specTerm:term) => do
    let yamlStr ← liftTermElabM <| SpytialSpec.toYaml <$> evalSpytialSpec specTerm
    logInfo m!"{yamlStr}"
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.datum <term>` prints the generated JSON data instance.
    Shows what atoms and relations the relationalizer produces. -/
syntax (name := spytialDatumDebug) "#spytial.datum " term : command

@[command_elab spytialDatumDebug]
meta def elabSpytialDatumDebug : CommandElab := fun
  | `(#spytial.datum $t:term) => do
    let (_, di) ← liftTermElabM <| elabRelationalized t
    logInfo m!"{(toJson di).pretty}"
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Proof visualization -/

/-- `#spytial.proof <term>` visualizes a proof term without filtering Prop-typed fields.
    Unlike `#spytial` (data mode), this shows the full proof structure — sub-proofs,
    premises, and witnesses are all included as nodes and edges.

    Use `with [...]` to specify layout operations.
-/
syntax (name := spytialProofCmd) "#spytial.proof " term (" with " term)? : command

@[command_elab spytialProofCmd]
meta def elabSpytialProofCmd : CommandElab := fun
  | stx@`(#spytial.proof $t:term $[with $spec?]?) => do
    let props ← liftTermElabM <|
      spytialPayloadProps t (spec?.map (·.raw)) { filterProofs := false }
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.proof.datum <term>` prints the JSON data instance in proof mode. -/
syntax (name := spytialProofDatumDebug) "#spytial.proof.datum " term : command

@[command_elab spytialProofDatumDebug]
meta def elabSpytialProofDatumDebug : CommandElab := fun
  | `(#spytial.proof.datum $t:term) => do
    let (_, di) ← liftTermElabM <| elabRelationalized t { filterProofs := false }
    logInfo m!"{(toJson di).pretty}"
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
meta def elabSpytialTactic : Tactic := fun stx => do
  let props ← spytialPayloadProps stx[1] (withClauseSpec? stx[2])
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

/-! ## Proof tactic -/

/-- Leading parser for the `spytial.proof` tactic. A dotted atom never enters
    the token table — the lexer reads `spytial.proof` as one qualified
    identifier — so an atom-led rule can never fire; match the identifier by
    value instead. `includeIdent := true` indexes the rule under the parser
    table's ident bucket; without it the rule is never tried. (`#`-led command
    atoms take the symbol path and are unaffected.) -/
meta def spytialProofKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.proof" (includeIdent := true)

open Tactic in
/-- `spytial.proof <term>` visualizes a proof term in tactic mode,
    showing the full proof structure without filtering Prop-typed fields. -/
syntax (name := spytialProofTactic) spytialProofKw term (" with " term)? : tactic

open Tactic in
@[tactic spytialProofTactic]
meta def elabSpytialProofTactic : Tactic := fun stx => do
  let props ← spytialPayloadProps stx[1] (withClauseSpec? stx[2]) { filterProofs := false }
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

end

end SpytialLean
