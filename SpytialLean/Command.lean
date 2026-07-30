module

public import Lean
public import Lean.Elab.Command
public import Lean.Elab.Term
public import Lean.Elab.Tactic
public import Lean.Widget.UserWidget
public meta import SpytialLean.Types
public meta import SpytialLean.Spec
public meta import SpytialLean.Selector
public meta import SpytialLean.SelectorElab
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.Widget
public meta import SpytialLean.Attr

namespace SpytialLean

open Lean Elab Command Term Meta Widget

public section

/-! ## The op DSL

An op is a keyword ident followed by juxtaposed arguments — selectors, relation
names, direction/style idents, strings, numbers:

```
spytial_spec BDD [
  orientation {x, y : BDD | x->y in (lo + hi)} below,
  edgeColor lo "orange" dashed,
  atomColor {x : BDD | @:x = ff} "red",
  hideAtom String
]
```

The head ident dispatches interpretation, so op keywords need no token-table
entries; arguments are parsed uniformly (`spytial_sel` or a numeral) and each
position is interpreted per op — selector positions elaborate against the
target's `SelScope` with the op's arity expectation, field positions must name
known relations, and enumerated idents (directions, styles) are validated by
value. -/

declare_syntax_cat spytial_op

syntax spytialOpArg := num <|> spytial_sel

syntax (name := spytialOpStx) ident spytialOpArg* : spytial_op
/-- `attribute` is a reserved Lean keyword, so it cannot arrive as the head
    ident — give it its own rule with the keyword as the atom. -/
syntax (name := spytialAttrOp) "attribute " spytialOpArg* : spytial_op

/-! ### Argument interpretation -/

private meta def Direction.parse? : String → Option Direction
  | "above" => some .above
  | "below" => some .below
  | "left" => some .left
  | "right" => some .right
  | "directlyAbove" => some .directlyAbove
  | "directlyBelow" => some .directlyBelow
  | "directlyLeft" => some .directlyLeft
  | "directlyRight" => some .directlyRight
  | _ => none

private meta def EdgeStyle.parse? : String → Option EdgeStyle
  | "solid" => some .solid
  | "dashed" => some .dashed
  | "dotted" => some .dotted
  | _ => none

private meta def AlignDir.parse? : String → Option AlignDir
  | "horizontal" => some .horizontal
  | "vertical" => some .vertical
  | _ => none

private meta def RotationDir.parse? : String → Option RotationDir
  | "clockwise" => some .clockwise
  | "counterclockwise" => some .counterclockwise
  | _ => none

private meta structure OpArgs where
  opName : Syntax
  usage : String
  args : Array (TSyntax `spytialOpArg)

/-- Bare idents and string literals arrive as the named selector rules. -/
private meta def argInner (arg : TSyntax `spytialOpArg) : Syntax := arg.raw[0]

private meta def OpArgs.get (a : OpArgs) (i : Nat) : TermElabM Syntax := do
  if h : i < a.args.size then
    return argInner a.args[i]
  else
    throwErrorAt a.opName m!"missing argument {i + 1}; usage: {a.usage}"

private meta def OpArgs.get? (a : OpArgs) (i : Nat) : Option Syntax :=
  a.args[i]?.map argInner

private meta def OpArgs.checkNoExtra (a : OpArgs) (n : Nat) : TermElabM Unit := do
  if h : n < a.args.size then
    throwErrorAt a.args[n] m!"unexpected extra argument; usage: {a.usage}"

private meta def OpArgs.sel (a : OpArgs) (i : Nat) : TermElabM (TSyntax `spytial_sel) := do
  let inner ← a.get i
  if inner.isOfKind numLitKind then
    throwErrorAt inner m!"expected a selector; usage: {a.usage}"
  return ⟨inner⟩

private meta def OpArgs.ident? (a : OpArgs) (i : Nat) : Option Ident :=
  match a.get? i with
  | some inner => if inner.isOfKind ``selIdent then some ⟨inner[0]⟩ else none
  | none => none

private meta def OpArgs.ident (a : OpArgs) (i : Nat) (what : String) :
    TermElabM Ident := do
  match a.ident? i with
  | some x => return x
  | none => throwErrorAt (← a.get i) m!"expected {what}; usage: {a.usage}"

private meta def OpArgs.str? (a : OpArgs) (i : Nat) : Option String :=
  match a.get? i with
  | some inner =>
    if inner.isOfKind ``selStr then inner[0].isStrLit? else none
  | none => none

private meta def OpArgs.str (a : OpArgs) (i : Nat) (what : String) :
    TermElabM String := do
  match a.str? i with
  | some s => return s
  | none => throwErrorAt (← a.get i) m!"expected {what} (a string literal); usage: {a.usage}"

private meta def OpArgs.nat (a : OpArgs) (i : Nat) (what : String) : TermElabM Nat := do
  let inner ← a.get i
  match inner.isNatLit? with
  | some n => return n
  | none => throwErrorAt inner m!"expected {what} (a numeral); usage: {a.usage}"

private meta def parseEnum {α} (what : String) (parse : String → Option α)
    (values : String) (x : Ident) : TermElabM α := do
  match parse x.getId.toString with
  | some v => return v
  | none => throwErrorAt x m!"unknown {what} '{x.getId}' (expected {values})"

private meta def directionValues : String :=
  "above, below, left, right, directlyAbove, directlyBelow, directlyLeft, directlyRight"

private meta def OpArgs.style (a : OpArgs) (i : Nat) : TermElabM EdgeStyle := do
  match a.ident? i with
  | some x => parseEnum "edge style" EdgeStyle.parse? "solid, dashed, dotted" x
  | none => do
    if (a.get? i).isSome then
      throwErrorAt (← a.get i) m!"expected an edge style (solid, dashed, dotted); \
        usage: {a.usage}"
    return .solid

private meta def OpArgs.flagIdent (a : OpArgs) (i : Nat) (flagName : String) :
    TermElabM Bool := do
  match a.ident? i with
  | some x =>
    if x.getId.toString == flagName then
      return true
    else
      throwErrorAt x m!"expected '{flagName}'; usage: {a.usage}"
  | none => do
    if (a.get? i).isSome then
      throwErrorAt (← a.get i) m!"expected '{flagName}'; usage: {a.usage}"
    return false

/-! ### Op elaboration -/

/-- Returns the scope extended with any name the op introduces (groups,
    inferred edges). -/
meta def elabSpytialOp (scope : SelScope) (op : TSyntax `spytial_op) :
    TermElabM (SpytialOp × SelScope) := do
  let (name, head) ←
    if op.raw.isOfKind ``spytialOpStx then
      pure (op.raw[0].getId.toString, op.raw[0])
    else if op.raw.isOfKind ``spytialAttrOp then
      pure ("attribute", op.raw[0])
    else
      throwErrorAt op "unexpected op syntax"
  let argStxs : Array (TSyntax `spytialOpArg) := op.raw[1].getArgs.map (⟨·⟩)
  withRef head do
    let mkArgs (usage : String) : OpArgs := { opName := head, usage, args := argStxs }
    let sel (a : OpArgs) (i : Nat) (expect : ArityExpect) : TermElabM Sel := do
      elabSelector scope expect (← a.sel i)
    match name with
    | "orientation" => do
      let a := mkArgs "orientation <selector> <direction>+"
      let s ← sel a 0 .pair
      let mut dirs : List Direction := []
      if a.args.size < 2 then
        throwErrorAt head m!"missing direction; usage: {a.usage}"
      for i in [1:a.args.size] do
        let x ← a.ident i "a direction"
        dirs := dirs ++ [← parseEnum "direction" Direction.parse? directionValues x]
      return (.orientation s dirs, scope)
    | "align" => do
      let a := mkArgs "align <selector> horizontal|vertical"
      let s ← sel a 0 .pair
      let x ← a.ident 1 "an alignment direction"
      let d ← parseEnum "alignment direction" AlignDir.parse? "horizontal, vertical" x
      a.checkNoExtra 2
      return (.align s d, scope)
    | "cyclic" => do
      let a := mkArgs "cyclic <selector> [clockwise|counterclockwise]"
      let s ← sel a 0 .pair
      let d ← match a.ident? 1 with
        | some x =>
          parseEnum "rotation direction" RotationDir.parse? "clockwise, counterclockwise" x
        | none => do
          if (a.get? 1).isSome then
            throwErrorAt (← a.get 1) m!"expected a rotation direction (clockwise, \
              counterclockwise); usage: {a.usage}"
          pure RotationDir.clockwise
      a.checkNoExtra 2
      return (.cyclic s d, scope)
    | "group" => do
      let a := mkArgs "group <selector> <name> [edge]"
      let s ← sel a 0 .unaryOrPair
      let gname ← match a.ident? 1, a.str? 1 with
        | some x, _ => pure x.getId.toString
        | _, some s => pure s
        | _, _ => throwErrorAt head m!"missing group name; usage: {a.usage}"
      let addEdge ← a.flagIdent 2 "edge"
      a.checkNoExtra 3
      return (.group s gname addEdge, scope.introduce gname 1)
    | "hideAtom" => do
      let a := mkArgs "hideAtom <selector>"
      let s ← sel a 0 .unary
      a.checkNoExtra 1
      return (.hideAtom s, scope)
    | "size" => do
      let a := mkArgs "size <selector> <width> <height>"
      let s ← sel a 0 .unary
      let w ← a.nat 1 "a width"
      let h ← a.nat 2 "a height"
      a.checkNoExtra 3
      return (.size s w h, scope)
    | "atomColor" => do
      let a := mkArgs "atomColor <selector> <css-color>"
      let s ← sel a 0 .unary
      let c ← a.str 1 "a CSS color"
      a.checkNoExtra 2
      return (.atomColor s c, scope)
    | "edgeColor" => do
      let a := mkArgs "edgeColor <field> <css-color> [solid|dashed|dotted]"
      let f ← elabFieldName scope (← a.ident 0 "a relation name")
      let c ← a.str 1 "a CSS color"
      let st ← a.style 2
      a.checkNoExtra 3
      return (.edgeColor f c st, scope)
    | "hideField" => do
      let a := mkArgs "hideField <field>"
      let f ← elabFieldName scope (← a.ident 0 "a relation name")
      a.checkNoExtra 1
      return (.hideField f, scope)
    | "attribute" => do
      let a := mkArgs "attribute <field>"
      let f ← elabFieldName scope (← a.ident 0 "a relation name")
      a.checkNoExtra 1
      return (.attribute f, scope)
    | "icon" => do
      let a := mkArgs "icon <selector> <path> [labels]"
      let s ← sel a 0 .unary
      let p ← a.str 1 "an icon path"
      let labels ← a.flagIdent 2 "labels"
      a.checkNoExtra 3
      return (.icon s p labels, scope)
    | "tag" => do
      let a := mkArgs "tag <selector> <name> <value>"
      let s ← sel a 0 .unary
      let n ← a.str 1 "a tag name"
      let v ← a.str 2 "a tag value"
      a.checkNoExtra 3
      return (.tag s n v, scope)
    | "inferredEdge" => do
      let a := mkArgs "inferredEdge <name> <selector> [<css-color>] [solid|dashed|dotted]"
      let n := (← a.ident 0 "an edge name").getId.toString
      let s ← sel a 1 .pair
      let colorGiven := (a.str? 2).isSome
      let c := (a.str? 2).getD "#000000"
      let st ← a.style (if colorGiven then 3 else 2)
      a.checkNoExtra (if colorGiven then 4 else 3)
      return (.inferredEdge n s c st, scope.introduce n 2)
    | "flag" => do
      let a := mkArgs "flag <name>"
      let n := (← a.ident 0 "a flag name").getId.toString
      a.checkNoExtra 1
      return (.flag n, scope)
    | _ =>
      throwErrorAt head m!"unknown Spytial op '{name}'; known ops: align, atomColor, \
        attribute, cyclic, edgeColor, flag, group, hideAtom, hideField, icon, \
        inferredEdge, orientation, size, tag"

meta def elabSpytialOps (scope : SelScope) (ops : Array (TSyntax `spytial_op)) :
    TermElabM SpytialSpec := do
  let mut scope := scope
  let mut spec : Array SpytialOp := #[]
  for op in ops do
    let (o, scope') ← elabSpytialOp scope op
    spec := spec.push o
    scope := scope'
  return spec.toList

/-- A term whose type has no head constant gets a fully lenient scope. -/
meta def scopeForExpr (e : Expr) : MetaM SelScope := do
  match ← typeHead? (← inferType e) with
  | some n => SelScope.ofType n
  | none => return { root := `_anonymous, lenient := true }

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
      -- parents come nearest-first; compose root-first, self last
      let parents ← getAllParentStructures n
      let allNames := parents.reverse.toList ++ [n]
      match allNames.filterMap (getSpytialSpec? env ·) with
      | [] => return none
      | specs => return some specs.flatten
    else
      return getSpytialSpec? env n
  | _ => return none

private meta def elabTermInstantiated (t : Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Elaborate a term to a fully instantiated expression and relationalize it. -/
private meta def elabRelationalized (t : Syntax) (cfg : WalkConfig := {}) :
    TermElabM (Expr × JsonDataInstance) := do
  let e ← elabTermInstantiated t
  return (e, ← relationalize e cfg)

/-- An explicit `with [<ops>]` overrides the type's attached spec. The spec is
    rendered to its wire string once, here. -/
private meta def elabSpytialPayload (t : Syntax) (ops? : Option (Array (TSyntax `spytial_op)))
    (cfg : WalkConfig) : TermElabM (JsonDataInstance × Option String) := do
  let (e, di) ← elabRelationalized t cfg
  let spec? ← match ops? with
    | some ops => do
      let scope ← scopeForExpr e
      pure (some (← elabSpytialOps scope ops))
    | none => lookupTypeSpec e
  return (di, spec?.map SpytialSpec.render)

private meta def spytialProps (di : JsonDataInstance) (cndSpec? : Option String) : Json :=
  Json.mkObj <|
    [("dataInstance", toJson di)] ++
    match cndSpec? with
    | some s => [("cndSpec", toJson s)]
    -- absent, not null: the widget reads a missing `cndSpec` as free layout
    | none => []

/-- The payload `#spytial` hands the infoview. Public so out-of-tree frontends
    render what the infoview does rather than reassembling it. -/
public meta def spytialPayloadProps (t : Syntax)
    (ops? : Option (Array (TSyntax `spytial_op)) := none) (cfg : WalkConfig := {}) :
    TermElabM Json := do
  let (di, cndSpec?) ← elabSpytialPayload t ops? cfg
  return spytialProps di cndSpec?

private meta def optionalOps (stx : Syntax) : Option (Array (TSyntax `spytial_op)) :=
  if stx.getNumArgs == 0 then none
  else some (stx[2].getSepArgs.map (⟨·⟩))

/-! ## #spytial command -/

/-- `#spytial <term>` displays a spatial relational diagram in the Lean infoview.

    Use `#spytial <term> with [<ops>]` to specify layout operations inline:
    ```
    #spytial myTree with [
      orientation left left below,
      atomColor leaf "#0066ff"
    ]
    ```

    If the type has an attached spec (via `spytial_spec`), it is used as the
    default. An explicit `with [...]` overrides it. -/
syntax (name := spytialCmd) "#spytial " term (" with " "[" spytial_op,* "]")? : command

@[command_elab spytialCmd]
meta def elabSpytialCmd : CommandElab := fun
  | stx@`(#spytial $t:term) => do
    let props ← liftTermElabM <| spytialPayloadProps t
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx@`(#spytial $t:term with [$ops,*]) => do
    let props ← liftTermElabM <| spytialPayloadProps t (some ops.getElems)
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx => throwError "Unexpected syntax {stx}."

/-! ## spytial_spec command -/

/-- `spytial_spec <Type> [<ops>]` attaches a Spytial layout spec to a type.
    The spec is used as the default when visualizing values of that type.

    ```
    spytial_spec Tree [
      orientation left left below,
      hideAtom Nat
    ]
    ```

    Selectors and field names are checked against the type's data vocabulary.
    The target resolves like any Lean name, so `open` works and renaming the
    type or a field causes a compile error. -/
syntax (name := spytialSpecCmd) "spytial_spec " ident " [" spytial_op,* "]" : command

@[command_elab spytialSpecCmd]
meta def elabSpytialSpecCmd : CommandElab := fun
  | `(spytial_spec $id:ident [$ops,*]) => do
    let declName ← resolveGlobalConstNoOverload id
    liftTermElabM do
      let scope ← SelScope.ofType declName
      let spec ← elabSpytialOps scope ops.getElems
      setSpytialSpec declName spec
  | stx => throwError "Unexpected syntax {stx}."

/-! ## spytial_relationalizer command -/

/-- `spytial_relationalizer <TypeName> <defName>` registers a custom relationalizer
    for a type. The def must have type `CustomRelationalizer`, and — to be usable
    from importing modules — should be `public meta def` (registration warns
    otherwise).

    ```
    public meta def myRelationalizer : CustomRelationalizer := fun e walkExpr => do ...

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
    if isPrivateName defName then
      logWarningAt defId m!"'{defName}' is not `public`, so a `#spytial` on this \
        type from an importing module fails at render with `Unknown constant` — \
        declare it `public meta def`"
    liftCoreM <| setSpytialRelationalizer typeName defName
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Debugging commands -/

/-- `#spytial.spec <term> with [<ops>]` prints the spec string handed to
    spytial-core. Useful for debugging whether the spec is what you expect. -/
syntax (name := spytialSpecDebug) "#spytial.spec " term " with " "[" spytial_op,* "]" : command

@[command_elab spytialSpecDebug]
meta def elabSpytialSpecDebug : CommandElab := fun
  | `(#spytial.spec $t:term with [$ops,*]) => do
    let specStr ← liftTermElabM do
      let scope ← scopeForExpr (← elabTermInstantiated t)
      let spec ← elabSpytialOps scope ops.getElems
      return spec.render
    logInfo m!"{specStr}"
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
syntax (name := spytialProofCmd) "#spytial.proof " term (" with " "[" spytial_op,* "]")? : command

@[command_elab spytialProofCmd]
meta def elabSpytialProofCmd : CommandElab := fun
  | stx@`(#spytial.proof $t:term) => do
    let props ← liftTermElabM <| spytialPayloadProps t none { filterProofs := false }
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx@`(#spytial.proof $t:term with [$ops,*]) => do
    let props ← liftTermElabM <|
      spytialPayloadProps t (some ops.getElems) { filterProofs := false }
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
syntax (name := spytialTactic) "spytial " term (" with " "[" spytial_op,* "]")? : tactic

open Tactic in
@[tactic spytialTactic]
meta def elabSpytialTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| spytial $t:term) => do
    let props ← spytialPayloadProps t
    savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | `(tactic| spytial $t:term with [$ops,*]) => do
    let props ← spytialPayloadProps t (some ops.getElems)
    savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | _ => throwError "Unexpected syntax {stx}."

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
syntax (name := spytialProofTactic) spytialProofKw term
  (" with " "[" spytial_op,* "]")? : tactic

open Tactic in
@[tactic spytialProofTactic]
meta def elabSpytialProofTactic : Tactic := fun stx => do
  -- Quotation patterns lex `spytial.proof` as a qualified ident and never match
  -- the ident-matched leading atom, so extract positionally.
  let props ← spytialPayloadProps stx[1] (optionalOps stx[2]) { filterProofs := false }
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

end

end SpytialLean
