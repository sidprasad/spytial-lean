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
public meta import SpytialLean.InContext
public meta import SpytialLean.ModelFind
public meta import SpytialLean.Widget
public meta import SpytialLean.Attr

namespace SpytialLean

open Lean Elab Command Term Meta Widget

public section

/-! ## The op DSL

The head ident dispatches interpretation, so op keywords need no token-table
entries. -/

declare_syntax_cat spytial_op
declare_syntax_cat spytial_block_arg
declare_syntax_cat spytial_op_block

syntax str : spytial_block_arg
syntax num : spytial_block_arg
syntax ident : spytial_block_arg
syntax spytial_op_block : spytial_block_arg

/-- `(blockName arg…)`: `atomic` through the first argument, so a
    parenthesized selector (`(lo)`, `(a + b)`) backtracks out to `spytial_sel`. -/
syntax (name := spytialBlockStx)
  atomic("(" ident spytial_block_arg) spytial_block_arg* ")" : spytial_op_block

syntax spytialOpArg := num <|> spytial_op_block <|> spytial_sel

syntax (name := spytialOpStx) ident spytialOpArg* : spytial_op
/-- `attribute` is a Lean keyword, so it gets its own rule with the keyword as the atom. -/
syntax (name := spytialAttrOp) "attribute " spytialOpArg* : spytial_op

/-! ### Argument interpretation -/

private meta structure OpArgs where
  opName : Syntax
  usage : String
  args : Array (TSyntax `spytialOpArg)

/-- Unwraps the `spytialOpArg` node to whichever of `num`/`spytial_sel` parsed. -/
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

private meta def enumValues (typeName : Name) : TermElabM String := do
  return ", ".intercalate ((← getConstInfoInduct typeName).ctors.map (·.getString!))

private meta def parseEnum {α} [FromJson α] (what : String) (typeName : Name)
    (x : Ident) : TermElabM α := do
  match fromJson? (Json.str x.getId.toString) with
  | .ok v => return v
  | .error _ =>
    throwErrorAt x m!"unknown {what} '{x.getId}' (expected {← enumValues typeName})"

/-! ### Style blocks -/

/-- One `(name arg…)` block, args classified by kind; block-argument order is
    free (a color is the string, a pattern the ident, a weight the numeral). -/
private meta structure BlockArgs where
  ref : Syntax
  name : String
  strs : Array (Syntax × String) := #[]
  nums : Array (Syntax × Nat) := #[]
  idents : Array (Syntax × Name) := #[]
  blocks : Array Syntax := #[]

/-- Node shape: `["(", ident, firstArg, args*, ")"]` (see `spytialBlockStx`). -/
private meta def BlockArgs.ofStx (stx : Syntax) : BlockArgs := Id.run do
  let mut b : BlockArgs := { ref := stx, name := stx[1].getId.toString }
  for arg in #[stx[2]] ++ stx[3].getArgs do
    let inner := arg[0]
    if let some s := inner.isStrLit? then b := { b with strs := b.strs.push (inner, s) }
    else if let some n := inner.isNatLit? then b := { b with nums := b.nums.push (inner, n) }
    else if inner.isIdent then b := { b with idents := b.idents.push (inner, inner.getId) }
    else b := { b with blocks := b.blocks.push inner }
  return b

private meta def atMostOne {α} (b : BlockArgs) (what : String)
    (xs : Array (Syntax × α)) : TermElabM (Option (Syntax × α)) := do
  if h : 1 < xs.size then
    throwErrorAt xs[1].1 m!"duplicate {what} in ({b.name} …)"
  return xs[0]?

private meta def rejectArgs {α} (b : BlockArgs) (kind : String)
    (xs : Array (Syntax × α)) : TermElabM Unit := do
  if h : 0 < xs.size then
    throwErrorAt xs[0].1 m!"({b.name} …) takes no {kind}"

private meta def rejectNested (b : BlockArgs) : TermElabM Unit := do
  if h : 0 < b.blocks.size then
    throwErrorAt b.blocks[0] m!"({b.name} …) takes no nested blocks"

private meta def parseBorderStyle (b : BlockArgs) : TermElabM BorderStyle := do
  rejectArgs b "idents" b.idents; rejectNested b
  let color ← atMostOne b "color" b.strs
  let width ← atMostOne b "width" b.nums
  return { color := color.map (·.2), width := width.map (·.2) }

private meta def parseFillStyle (b : BlockArgs) : TermElabM FillStyle := do
  rejectArgs b "idents" b.idents; rejectArgs b "numerals" b.nums; rejectNested b
  let color ← atMostOne b "color" b.strs
  return { color := color.map (·.2) }

private meta def parseIconStyle (b : BlockArgs) : TermElabM IconStyle := do
  rejectArgs b "numerals" b.nums; rejectNested b
  let some path ← atMostOne b "path" b.strs
    | throwErrorAt b.ref m!"(iconStyle …) needs a path string"
  let placement ← match ← atMostOne b "placement" b.idents with
    | some (stx, _) => some <$> parseEnum "icon placement" ``IconPlacement ⟨stx⟩
    | none => pure none
  return { path := path.2, placement }

private meta def parseLineStyle (b : BlockArgs) : TermElabM LineStyle := do
  rejectNested b
  let color ← atMostOne b "color" b.strs
  let weight ← atMostOne b "weight" b.nums
  let pattern ← match ← atMostOne b "pattern" b.idents with
    | some (stx, _) => some <$> parseEnum "line pattern" ``LinePattern ⟨stx⟩
    | none => pure none
  return { color := color.map (·.2), pattern, weight := weight.map (·.2) }

private meta def parseGroupEdge (b : BlockArgs) : TermElabM GroupEdge := do
  rejectArgs b "strings" b.strs; rejectArgs b "numerals" b.nums
  let some dir ← atMostOne b "direction" b.idents
    | throwErrorAt b.ref m!"(addEdge …) needs a direction \
        ({← enumValues ``GroupEdgeDirection})"
  let direction ← parseEnum "group-edge direction" ``GroupEdgeDirection ⟨dir.1⟩
  let lineStyle ← match ← atMostOne b "nested block" (b.blocks.map ((·, ()))) with
    | some (stx, _) =>
      let nb := BlockArgs.ofStx stx
      unless nb.name == "lineStyle" do
        throwErrorAt stx m!"(addEdge …) nests only (lineStyle …)"
      some <$> parseLineStyle nb
    | none => pure none
  return { direction, lineStyle }

/-- The style pieces an op's trailing arguments can carry. -/
private meta structure StyleParts where
  border : Option BorderStyle := none
  fill : Option FillStyle := none
  icon : Option IconStyle := none
  line : Option LineStyle := none
  addEdge : Option GroupEdge := none
  showLabel : Option Bool := none

/-- Fold the arguments from `start` on: `(block …)`s from `allowed`, plus the
    `labels`/`noLabels` flags when `flags` is set. -/
private meta def collectStyleArgs (a : OpArgs) (start : Nat)
    (allowed : List String) (flags : Bool := false) : TermElabM StyleParts := do
  let dup {α} (stx : Syntax) (what : String) : Option α → TermElabM Unit := fun
    | some _ => throwErrorAt stx m!"duplicate {what}; usage: {a.usage}"
    | none => pure ()
  let mut parts : StyleParts := {}
  for i in [start:a.args.size] do
    let inner := argInner a.args[i]!
    if inner.isOfKind ``spytialBlockStx then
      let b := BlockArgs.ofStx inner
      unless allowed.contains b.name do
        throwErrorAt inner m!"unknown block '({b.name} …)'; expected \
          {", ".intercalate (allowed.map (s!"({·} …)"))}; usage: {a.usage}"
      match b.name with
      | "borderStyle" => dup inner "(borderStyle …)" parts.border
                         parts := { parts with border := some (← parseBorderStyle b) }
      | "fillStyle"   => dup inner "(fillStyle …)" parts.fill
                         parts := { parts with fill := some (← parseFillStyle b) }
      | "iconStyle"   => dup inner "(iconStyle …)" parts.icon
                         parts := { parts with icon := some (← parseIconStyle b) }
      | "lineStyle"   => dup inner "(lineStyle …)" parts.line
                         parts := { parts with line := some (← parseLineStyle b) }
      | "addEdge"     => dup inner "(addEdge …)" parts.addEdge
                         parts := { parts with addEdge := some (← parseGroupEdge b) }
      | _ => throwErrorAt inner "unexpected block"
    else if flags && inner.isOfKind ``selIdent &&
        (inner[0].getId.toString == "labels" || inner[0].getId.toString == "noLabels") then
      dup inner "label flag" parts.showLabel
      parts := { parts with showLabel := some (inner[0].getId.toString == "labels") }
    else
      throwErrorAt inner m!"expected a style block\
        {if flags then " or labels|noLabels" else ""}; usage: {a.usage}"
  return parts

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
        dirs := dirs ++ [← parseEnum "direction" ``Direction x]
      return (.orientation s dirs, scope)
    | "align" => do
      let a := mkArgs "align <selector> horizontal|vertical"
      let s ← sel a 0 .pair
      let x ← a.ident 1 "an alignment direction"
      let d ← parseEnum "alignment direction" ``AlignDir x
      a.checkNoExtra 2
      return (.align s d, scope)
    | "cyclic" => do
      let a := mkArgs "cyclic <selector> [clockwise|counterclockwise]"
      let s ← sel a 0 .pair
      let d ← match a.ident? 1 with
        | some x =>
          parseEnum "rotation direction" ``RotationDir x
        | none => do
          if (a.get? 1).isSome then
            throwErrorAt (← a.get 1) m!"expected a rotation direction \
              ({← enumValues ``RotationDir}); usage: {a.usage}"
          pure RotationDir.clockwise
      a.checkNoExtra 2
      return (.cyclic s d, scope)
    | "group" => do
      let a := mkArgs "group <selector> <name> [(addEdge togroup|fromgroup (lineStyle …)?)]"
      let s ← sel a 0 .unaryOrPair
      let gname ← match a.ident? 1, a.str? 1 with
        | some x, _ => pure x.getId.toString
        | _, some s => pure s
        | _, _ => throwErrorAt head m!"missing group name; usage: {a.usage}"
      let p ← collectStyleArgs a 2 ["addEdge"]
      return (.group s gname p.addEdge, scope.introduce gname 1)
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
    | "atomStyle" => do
      let a := mkArgs "atomStyle <selector> (borderStyle <color> [<width>])? \
        (fillStyle <color>)? (iconStyle <path> [full|badge])? [labels|noLabels]"
      let s ← sel a 0 .unary
      let p ← collectStyleArgs a 1 ["borderStyle", "fillStyle", "iconStyle"] (flags := true)
      if p.border.isNone && p.fill.isNone && p.icon.isNone && p.showLabel.isNone then
        throwErrorAt head m!"atomStyle sets nothing; usage: {a.usage}"
      return (.atomStyle s p.border p.fill p.icon p.showLabel, scope)
    | "edgeStyle" => do
      let a := mkArgs "edgeStyle <field> (lineStyle <color> [solid|dashed|dotted] \
        [<weight>])? [labels|noLabels]"
      let f ← elabFieldName scope (← a.ident 0 "a relation name")
      let p ← collectStyleArgs a 1 ["lineStyle"] (flags := true)
      if p.line.isNone && p.showLabel.isNone then
        throwErrorAt head m!"edgeStyle sets nothing; usage: {a.usage}"
      return (.edgeStyle f p.line p.showLabel, scope)
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
    | "tag" => do
      let a := mkArgs "tag <selector> <name> <value>"
      let s ← sel a 0 .unary
      let n ← a.str 1 "a tag name"
      let v ← a.str 2 "a tag value"
      a.checkNoExtra 3
      return (.tag s n v, scope)
    | "inferredEdge" => do
      let a := mkArgs "inferredEdge <name> <selector> (lineStyle <color> \
        [solid|dashed|dotted] [<weight>])?"
      let n := (← a.ident 0 "an edge name").getId.toString
      let s ← sel a 1 .edge
      let p ← collectStyleArgs a 2 ["lineStyle"]
      return (.inferredEdge n s p.line, scope.introduce n 2)
    | "flag" => do
      let a := mkArgs "flag <name>"
      let n := (← a.ident 0 "a flag name").getId.toString
      a.checkNoExtra 1
      return (.flag n, scope)
    | _ =>
      throwErrorAt head m!"unknown Spytial op '{name}'; known ops: align, atomStyle, \
        attribute, cyclic, edgeStyle, flag, group, hideAtom, hideField, \
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
      atomStyle leaf "#0066ff"
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
-/
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
    from importing modules — should be `public meta def`.

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

/-! ## spytial tactic: a value drawn with what the context knows about it

In tactic position the subject sits in a live local context, and that context
knows things about it: refinements (equations, `let` bindings, elaborator
assignments) and Prop facts. `spytialInContextProps` is the tactic-side
sibling of `spytialPayloadProps` — same payload shape, context knowledge
folded in. -/

/-- Default styling for negative relations (`≠`, `¬R`): dashed red edges, the
    ruled-out look. Prepended before user ops, so an explicit `with [...]`
    overrides. Sorted for a deterministic spec string. -/
private meta def negativeStyleOps (di : JsonDataInstance) : SpytialSpec :=
  let names := di.relations.filterMap fun r =>
    if isNegativeRelName r.name then some r.name else none
  names.qsort (· < ·) |>.toList.map fun n =>
    .edgeStyle n (line := some { color := some "#cc0000", pattern := some .dashed })

/-- The payload the `spytial` tactic hands the infoview: the subject walked
    together with what the local context knows about it (`walkInContext`),
    plus the count of subject-relevant Prop hypotheses that did not decompose
    (the caller reports them). An explicit `with [<ops>]` overrides the
    subject type's attached `spytial_spec`, exactly like `#spytial`; ops
    elaborate against the subject type's scope extended with the fact
    vocabulary (`scopeInContext`). Either way, the default negative-relation
    styling is prepended when negative relations were emitted, so explicit
    ops override it. -/
public meta def spytialInContextProps (subject : Expr)
    (ops? : Option (Array (TSyntax `spytial_op)) := none)
    (cfg : WalkConfig := {}) : TermElabM (Json × Nat) := do
  let (skipped, state) ← (walkInContext cfg subject).run {}
  let di := state.toDataInstance
  let defaults := negativeStyleOps di
  let spec ← match ops? with
    | some ops => do
      pure (defaults ++ (← elabSpytialOps (← scopeInContext subject) ops))
    | none => pure (defaults ++ ((← lookupTypeSpec subject).getD []))
  let spec? := if spec.isEmpty then none else some (SpytialSpec.render spec)
  return (spytialProps di spec?, skipped)

open Tactic in
/-- Shared body of the context-aware tactic arms: elaborate the subject in
    the main goal's context (hypotheses introduced by earlier tactics live
    there, not in the by-block's ambient one), build the payload, report
    skipped facts, render. -/
private meta def spytialInContextTac (t : Syntax)
    (ops? : Option (Array (TSyntax `spytial_op))) (stx : Syntax) :
    TacticM Unit := do
  let (props, skipped) ← withMainContext do
    spytialInContextProps (← elabTermInstantiated t) ops?
  if skipped > 0 then
    logInfo m!"spytial: skipped {skipped} hypothesis(es) about the subject \
      that do not decompose into relation tuples (e.g. `∀`, `∧`)."
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

open Tactic in
/-- `spytial <term>` displays a spatial relational diagram in the Lean
    infoview during tactic mode — the value drawn with everything the local
    context knows about it:

    - Metavariable assignments are instantiated: structure the elaborator has
      already determined (a `refine`, a `let`) draws as structure, with the
      still-open holes as atoms inside it.
    - `h : x = t` (and `let x := t`) refines `x`: its atom shows `t`'s
      structure instead of an opaque leaf.
    - A Prop hypothesis mentioning the subject becomes a relation tuple
      anchored on its atoms: `h : R x y` in relation `R`; `h : x ≠ t` and
      `h : ¬ P x` in the ruled-out relations `≠` / `¬P`, drawn dashed red by
      default.
    - Hypotheses not mentioning the subject are ignored; subject-relevant
      Props that do not decompose (`∀ …`, `A ∧ B`) are skipped, with one note
      reporting the count.

    The goal is deliberately not drawn: hypotheses are established knowledge,
    the goal is what is still being proven.

    `spytial <term> with [<ops>]` specifies layout operations, just like the
    `#spytial` command; without ops, the subject type's `spytial_spec`
    applies. Negative relation names are addressable in field positions as
    escaped idents (`edgeStyle «≠» …`); they cannot occur inside selector
    expressions — the query language cannot lex them.

    ```
    example (t : RBTree Nat) (h : t ≠ .leaf) : True := by
      spytial t
      trivial
    ```
-/
syntax (name := spytialTactic) "spytial " term (" with " "[" spytial_op,* "]")? : tactic

open Tactic in
@[tactic spytialTactic]
meta def elabSpytialTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| spytial $t:term) => spytialInContextTac t none stx
  | `(tactic| spytial $t:term with [$ops,*]) => spytialInContextTac t (some ops.getElems) stx
  | _ => throwError "Unexpected syntax {stx}."

meta def spytialDatumKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.datum" (includeIdent := true)

open Tactic in
/-- `spytial.datum <term>` prints the JSON data instance the `spytial` tactic
    would draw — the debugging counterpart, mirroring `#spytial.datum`. -/
syntax (name := spytialDatumTactic) spytialDatumKw term : tactic

open Tactic in
@[tactic spytialDatumTactic]
meta def elabSpytialDatumTactic : Tactic := fun stx => do
  withMainContext do
    let subject ← elabTermInstantiated stx[1]
    let (_, state) ← (walkInContext {} subject).run {}
    logInfo m!"{(toJson state.toDataInstance).pretty}"

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
  -- A quotation pattern would lex `spytial.proof` as one dotted ident and never
  -- match; extract positionally.
  let props ← withMainContext do
    spytialPayloadProps stx[1] (optionalOps stx[2]) { filterProofs := false }
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

/-! ## Model finding -/

/-- Default constructor-depth bound for `spytial.find`. -/
meta def defaultFindDepth : Nat := 3

/-- Run the bounded search for `spytial.find`: resolve the subject to a local
    variable, search, report, and return the walk config with the first model
    injected as a refinement (unchanged when nothing was found). -/
private meta def runFindSearch (subjStx : Syntax) (depthStx : Syntax) :
    TermElabM (Expr × WalkConfig) := do
  let e ← Term.elabTerm subjStx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let .fvar fvarId := e
    | throwErrorAt subjStx m!"spytial.find expects a local variable (the hole \
        to search for), got {e}"
  let depth := if depthStx.getNumArgs == 0 then defaultFindDepth
    else (depthStx[0].isNatLit?).getD defaultFindDepth
  let search ← findModels fvarId depth
  if search.candidates == 0 then
    logWarningAt subjStx m!"spytial.find: cannot enumerate values of \
      {← inferType e} — the diagram shows the hole as known, without a model."
    return (e, {})
  let atLeast := if search.capped then "at least " else ""
  let uncheckedNote :=
    if search.unchecked == 0 then m!""
    else m!" ({search.unchecked} hypothesis(es) unchecked: no decision \
      procedure, or no candidates left to decide on)"
  match search.models[0]? with
  | some m =>
    logInfo m!"spytial.find: {search.models.size} of {atLeast}{search.candidates} \
      candidate(s) at depth ≤ {depth} satisfy all {search.checked} checked \
      hypothesis(es){uncheckedNote}; showing the first."
    return (e, { refinements := ({} : Std.HashMap FVarId Expr).insert fvarId m })
  | none =>
    logWarningAt subjStx m!"spytial.find: no candidate at depth ≤ {depth} \
      satisfies the {search.checked} checked hypothesis(es) — \
      {atLeast}{search.candidates} candidate(s) ruled out{uncheckedNote}. \
      The diagram shows the hole as known, without a model."
    return (e, {})

meta def spytialFindKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.find" (includeIdent := true)

open Tactic in
/-- `spytial.find x` searches for concrete values the hole `x` can be, and
    draws one.

    Candidates are every value of `x`'s type up to a constructor depth
    (default `3`; `spytial.find x 5` raises it), Alloy-style scope-bounded
    enumeration. A candidate survives when every hypothesis mentioning `x`
    that has a decision procedure (`Decidable` after substituting the
    candidate — so `x ≠ t` needs `DecidableEq`) evaluates to true.
    Hypotheses that cannot be decided are reported as *unchecked*, never
    silently assumed.

    The first surviving model is injected as a refinement and `x` is drawn
    as by the `spytial` tactic: the model's structure, with every fact —
    relations, `≠` edges — anchored on it. When nothing survives the bound,
    that is the finding: the hole cannot look like any candidate, and the
    diagram falls back to what is known.

    `with [<ops>]` attaches layout ops, as in the `spytial` tactic. -/
syntax (name := spytialFindTactic) spytialFindKw (colGt ident)? (num)?
  (" with " "[" spytial_op,* "]")? : tactic

open Tactic in
@[tactic spytialFindTactic]
meta def elabSpytialFindTactic : Tactic := fun stx => do
  if stx[1].getNumArgs == 0 then
    throwError "spytial.find expects the local variable to search for: `spytial.find x`"
  let (props, skipped) ← withMainContext do
    let (subject, cfg) ← runFindSearch stx[1][0] stx[2]
    spytialInContextProps subject (optionalOps stx[3]) cfg
  if skipped > 0 then
    logInfo m!"spytial.find: skipped {skipped} hypothesis(es) that do not \
      decompose into relation tuples (e.g. `∀`, `∧`, `→`)."
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

meta def spytialFindDatumKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.find.datum" (includeIdent := true)

open Tactic in
/-- `spytial.find.datum x` prints the JSON data instance `spytial.find x`
    would draw — the debugging counterpart. -/
syntax (name := spytialFindDatumTactic) spytialFindDatumKw (colGt ident)? (num)? : tactic

open Tactic in
@[tactic spytialFindDatumTactic]
meta def elabSpytialFindDatumTactic : Tactic := fun stx => do
  if stx[1].getNumArgs == 0 then
    throwError "spytial.find.datum expects the local variable to search for"
  withMainContext do
    let (subject, cfg) ← runFindSearch stx[1][0] stx[2]
    let (_, state) ← (walkInContext cfg subject).run {}
    logInfo m!"{(toJson state.toDataInstance).pretty}"

end

end SpytialLean
