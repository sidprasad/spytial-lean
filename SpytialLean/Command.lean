module

public import SpytialLean.Enum
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
public meta import SpytialLean.LeanSelector
public meta import SpytialLean.Widget
public meta import SpytialLean.Attr
public meta import Iykyk.Tactic

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
/-- In a use-site `with [...]`, `..` splices the type's attached spec at that position. -/
syntax (name := spytialSpliceStx) ".." : spytial_op
/-- `..name` splices the op list bound by `spytial_ops name` at that position,
    which must have been bound against the same root type. -/
syntax (name := spytialSpliceNamedStx) ".." noWs ident : spytial_op

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

meta def elabSpytialOp (scope : SelScope) (op : TSyntax `spytial_op) :
    TermElabM SpytialOp := do
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
      return .orientation s dirs
    | "align" => do
      let a := mkArgs "align <selector> horizontal|vertical"
      let s ← sel a 0 .pair
      let x ← a.ident 1 "an alignment direction"
      let d ← parseEnum "alignment direction" ``AlignDir x
      a.checkNoExtra 2
      return .align s d
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
      return .cyclic s d
    | "group" => do
      let a := mkArgs "group <selector> <name> [(addEdge togroup|fromgroup (lineStyle …)?)]"
      let s ← sel a 0 .unaryOrPair
      let gname ← match a.ident? 1, a.str? 1 with
        | some x, _ => pure (x.getId.toString (escape := false))
        | _, some s => pure s
        | _, _ => throwErrorAt head m!"missing group name; usage: {a.usage}"
      let p ← collectStyleArgs a 2 ["addEdge"]
      return .group s gname p.addEdge
    | "hideAtom" => do
      let a := mkArgs "hideAtom <selector>"
      let s ← sel a 0 .unary
      a.checkNoExtra 1
      return .hideAtom s
    | "size" => do
      let a := mkArgs "size <selector> <width> <height>"
      let s ← sel a 0 .unary
      let w ← a.nat 1 "a width"
      let h ← a.nat 2 "a height"
      a.checkNoExtra 3
      return .size s w h
    | "atomStyle" => do
      let a := mkArgs "atomStyle <selector> (borderStyle <color> [<width>])? \
        (fillStyle <color>)? (iconStyle <path> [full|badge])? [labels|noLabels]"
      let s ← sel a 0 .unary
      let p ← collectStyleArgs a 1 ["borderStyle", "fillStyle", "iconStyle"] (flags := true)
      if p.border.isNone && p.fill.isNone && p.icon.isNone && p.showLabel.isNone then
        throwErrorAt head m!"atomStyle sets nothing; usage: {a.usage}"
      return .atomStyle s p.border p.fill p.icon p.showLabel
    | "edgeStyle" => do
      let a := mkArgs "edgeStyle <field> (lineStyle <color> [solid|dashed|dotted] \
        [<weight>])? [labels|noLabels]"
      let f ← elabFieldName scope (← a.ident 0 "a relation name")
      let p ← collectStyleArgs a 1 ["lineStyle"] (flags := true)
      if p.line.isNone && p.showLabel.isNone then
        throwErrorAt head m!"edgeStyle sets nothing; usage: {a.usage}"
      return .edgeStyle f p.line p.showLabel
    | "hideField" => do
      let a := mkArgs "hideField <field>"
      let f ← elabFieldName scope (← a.ident 0 "a relation name")
      a.checkNoExtra 1
      return .hideField f
    | "attribute" => do
      let a := mkArgs "attribute <field>"
      let f ← elabFieldName scope (← a.ident 0 "a relation name")
      a.checkNoExtra 1
      return .attribute f
    | "tag" => do
      let a := mkArgs "tag <selector> <name> <value>"
      let s ← sel a 0 .unary
      let n ← a.str 1 "a tag name"
      let v ← a.str 2 "a tag value"
      a.checkNoExtra 3
      return .tag s n v
    | "inferredEdge" => do
      let a := mkArgs "inferredEdge <name> <selector> (lineStyle <color> \
        [solid|dashed|dotted] [<weight>])?"
      let n := (← a.ident 0 "an edge name").getId.toString (escape := false)
      let s ← sel a 1 .edge
      let p ← collectStyleArgs a 2 ["lineStyle"]
      return .inferredEdge n s p.line
    | "flag" => do
      let a := mkArgs "flag <name>"
      let n := (← a.ident 0 "a flag name").getId.toString (escape := false)
      a.checkNoExtra 1
      return .flag n
    | _ =>
      throwErrorAt head m!"unknown Spytial op '{name}'; known ops: align, atomStyle, \
        attribute, cyclic, edgeStyle, flag, group, hideAtom, hideField, \
        inferredEdge, orientation, size, tag"

/-- The op as the user wrote it, with where they wrote it. Read back from the
    file rather than reprinted from syntax, so what core cites in a conflict
    report is the text on the line. -/
private meta def opSource? (op : TSyntax `spytial_op) : TermElabM (Option OpSource) := do
  unless spytial.source.get (← getOptions) do return none
  let some startPos := op.raw.getPos? | return none
  let some endPos := op.raw.getTailPos? | return none
  let fileMap ← getFileMap
  let text := (Substring.Raw.mk fileMap.source startPos endPos).toString.trim
  if text.isEmpty then return none
  let path := (← getFileName)
  let base := (System.FilePath.mk path).fileName.getD path
  return some { text, location := s!"{base}:{(fileMap.toPosition startPos).line}" }

/-- Elaborate an op list, bringing each op's introduced names (groups, inferred
    edges) into scope for the ops after it. A `..` element splices `attached?`
    at that position; `none` means the context has no attached spec to splice.
    A `..name` element splices the op list bound by `spytial_ops name`, which
    must share this list's root type. -/
meta def elabSpytialOps (scope : SelScope) (ops : Array (TSyntax `spytial_op))
    (attached? : Option SpytialSpec := none) : TermElabM SpytialSpec := do
  let introduce (scope : SelScope) (s : StampedOp) : SelScope :=
    match s.op.introduces? with
    | some (n, arity) => scope.introduce n arity
    | none => scope
  let mut scope := scope
  let mut spec : Array StampedOp := #[]
  let mut spliced := false
  let mut splicedNames : NameSet := .empty
  for op in ops do
    if op.raw.isOfKind ``spytialSpliceStx then
      let some attached := attached?
        | throwErrorAt op "`..` splices the type's attached spec; \
            only a use-site `with [...]` has one"
      if spliced then
        throwErrorAt op "duplicate `..`"
      spliced := true
      spec := spec ++ attached
      scope := attached.foldl introduce scope
    else if op.raw.isOfKind ``spytialSpliceNamedStx then
      let id : Ident := ⟨op.raw[1]⟩
      let name ← realizeGlobalConstNoOverloadWithInfo id
      let some bound := getSpytialOps? (← getEnv) name
        | throwErrorAt id m!"'{name}' is not a `spytial_ops` declaration; \
            `spytial_ops <name> : <RootType> [<ops>]` binds one"
      -- `_anonymous` is the scrutinee with no type head: no root to check against
      unless bound.root == scope.root || scope.root == `_anonymous do
        throwErrorAt id m!"'{name}' is bound against '{bound.root}', but this op \
          list is elaborated against '{scope.root}'"
      if splicedNames.contains name then
        throwErrorAt id m!"duplicate `..{name}`"
      splicedNames := splicedNames.insert name
      spec := spec ++ bound.ops
      scope := bound.ops.foldl introduce scope
    else
      let o : StampedOp := { op := ← elabSpytialOp scope op, source := ← opSource? op }
      spec := spec.push o
      scope := introduce scope o
  return spec.toList

/-- A term whose type has no head constant gets a fully lenient scope. -/
meta def scopeForExpr (e : Expr) : MetaM SelScope := do
  let ty ← inferType e
  match ← typeHead? ty with
  | some n =>
    let seeds ← ty.getAppArgs.filterMapM fun a => do
      if (← Meta.whnf (← inferType a)) matches .sort _ then typeHead? a else pure none
    SelScope.ofType n seeds
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

/-- Elaborate named unary data functions into requested applications. Their
    function heads later parameterize relationalization of the root and any
    proof-context expressions. -/
private meta def resolveObservationTerms (subject : Expr) (observerSyntaxes : Array Syntax) :
    TermElabM (Array Expr) :=
  observerSyntaxes.mapM fun observerSyntax => do
    let observer ← elabTermInstantiated observerSyntax
    let observation ← try
      mkAppM' observer #[subject]
    catch _ =>
      throwErrorAt observerSyntax m!"'observing' expects a unary function applicable to \
        the selected value, but '{observerSyntax}' has type {← inferType observer}"
    if ← isProp observation then
      throwErrorAt observerSyntax "'observing' expects a data-returning function, not a predicate"
    let resultType ← whnf (← inferType observation)
    if resultType.isForall then
      throwErrorAt observerSyntax "'observing' expects a unary function"
    if resultType.isSort then
      throwErrorAt observerSyntax "'observing' expects a function returning a data value"
    unless (← graphSide? observation).isSome do
      throwErrorAt observerSyntax "'observing' expects a named function"
    return observation

private meta def resolveObservations (subject : Expr) (stx : Syntax) :
    TermElabM (Array Expr) :=
  if stx.getNumArgs == 0 then pure #[]
  else resolveObservationTerms subject stx[2].getSepArgs

/-- Elaborate a term to a fully instantiated expression and relationalize it,
    keeping the provenance raw Lean selectors resolve against. -/
private meta def elabRelationalized (t : Syntax) (cfg : WalkConfig := {})
    (observerSyntaxes : Array Syntax := #[]) :
    TermElabM (Expr × Array Expr × JsonDataInstance × Provenance × SelectorEvidence) := do
  let e ← elabTermInstantiated t
  let observations ← resolveObservationTerms e observerSyntaxes
  let (di, prov, evidence) ← relationalizeWithEvidence e cfg observations
  return (e, observations, di, prov, evidence)

/-- Elaborate a use-site `with [...]` for `e`. Without `..` the list replaces
    `e`'s attached spec; a `..` element splices the attached spec at that
    position, its introduced names in scope for the ops after it. `scope?`
    overrides the scope for callers that know more than `e`'s type does. -/
private meta def elabUseSiteOps (e : Expr) (ops : Array (TSyntax `spytial_op))
    (scope? : Option SelScope := none) : TermElabM SpytialSpec := do
  let attached? ← lookupTypeSpec e
  if attached?.isNone then
    if let some splice := ops.find? (·.raw.isOfKind ``spytialSpliceStx) then
      logWarningAt splice m!"`..` splices the attached spec, but {← inferType e} has none"
  elabSpytialOps (← scope?.getDM (scopeForExpr e)) ops (some (attached?.getD []))

/-- Extend a value's ordinary selector scope with explicitly requested
    function graphs. -/
private meta def scopeForObservations (base : SelScope) (observations : Array Expr) :
    MetaM SelScope := do
  let mut scope := base
  let mut relations := #[]
  let mut heads := #[]
  for observation in observations do
    if let some (name, arguments) ← graphSide? observation then
      relations := relations.push (name, arguments.size + 1)
      for argument in arguments.push observation do
        heads := heads.push (← typeHead? (← inferType argument))
  for head in heads.filterMap id do
    scope := scope.merge (← SelScope.ofType head)
  for (name, arity) in relations do
    scope := { scope with rels :=
      match scope.rels.get? name with
      | some (owner, some previous) =>
          if previous == arity then scope.rels else scope.rels.insert name (owner, none)
      | some (_, none) => scope.rels
      | none => scope.rels.insert name (scope.root, some arity) }
  return { scope with lenient := scope.lenient || heads.contains none }

/-- Observation reduction can expose computations absent from the root type
    and the original facts. Their emitted vocabulary is still checked at its
    actual arity, rather than making the whole selector scope lenient. -/
private meta def scopeWithObservedData (scope : SelScope) (data : JsonDataInstance) :
    SelScope := Id.run do
  let mut scope := scope
  for relation in data.relations do
    unless scope.rels.contains relation.name do
      scope := { scope with
        rels := scope.rels.insert relation.name (scope.root, some relation.types.size) }
  return scope

/-- An explicit `with [<ops>]` overrides the type's attached spec, unless a
    `..` element splices it back in. Raw Lean selectors resolve against this
    datum, and the spec is rendered to its wire string once, here. -/
private meta def elabSpytialPayload (t : Syntax) (ops? : Option (Array (TSyntax `spytial_op)))
    (cfg : WalkConfig) (observerSyntaxes : Array Syntax := #[]) :
    TermElabM (JsonDataInstance × Option String) :=
  -- The command boundary is where `#eval` discards what it derived, and both
  -- halves below derive: the walk needs `SpytialIdentity`, and building the
  -- selector scope needs `SpytialEnum`. Wrapping only the walk would leave the
  -- spec half persisting its instances. Both results are plain data.
  withoutModifyingEnv do
    let (e, observations, di, prov, evidence) ← elabRelationalized t cfg observerSyntaxes
    let spec? ← match ops? with
      | some ops => do
        let scope ← scopeForObservations (← scopeForExpr e) observations
        let scope := if observations.isEmpty then scope else scopeWithObservedData scope di
        some <$> elabUseSiteOps e ops (some scope)
      | none => lookupTypeSpec e
    let spec? ← spec?.mapM fun s => liftM (resolveLeanSelectors e di prov s evidence)
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
    (ops? : Option (Array (TSyntax `spytial_op)) := none) (cfg : WalkConfig := {})
    (observerSyntaxes : Array Syntax := #[]) :
    TermElabM Json := do
  let (di, cndSpec?) ← elabSpytialPayload t ops? cfg observerSyntaxes
  return spytialProps di cndSpec?

private meta def optionalOps (stx : Syntax) : Option (Array (TSyntax `spytial_op)) :=
  if stx.getNumArgs == 0 then none
  else some (stx[2].getSepArgs.map (⟨·⟩))

private meta def optionalTerms (stx : Syntax) : Array Syntax :=
  if stx.getNumArgs == 0 then #[] else stx[2].getSepArgs

/-! ## #spytial command -/

/-- `#spytial <term>` displays a spatial relational diagram in the Lean infoview.

    `observing [f₁, ...]` parameterizes the relationalizer with the named
    functions and adds each function's graph over every compatible value in
    the represented datum. Command mode has no proof context; tactic mode uses
    the same observation input while also translating context facts.

    Use `#spytial <term> with [<ops>]` to specify layout operations inline:
    ```
    #spytial myTree with [
      orientation left left below,
      atomStyle leaf "#0066ff"
    ]
    ```

    If the type has an attached spec (via `spytial_spec`), it is used as the
    default. An explicit `with [...]` overrides it; a `..` element in the list
    splices the attached spec at that position:
    ```
    #spytial myTree with [.., hideAtom Nat]
    ``` -/
syntax (name := spytialCmd) "#spytial " term (" observing " "[" term,* "]")?
  (" with " "[" spytial_op,*,? "]")? : command

@[command_elab spytialCmd]
meta def elabSpytialCmd : CommandElab := fun stx => do
  let props ← liftTermElabM <|
    spytialPayloadProps stx[1] (optionalOps stx[3]) {} (optionalTerms stx[2])
  liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

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
syntax (name := spytialSpecCmd) "spytial_spec " ident " [" spytial_op,*,? "]" : command

@[command_elab spytialSpecCmd]
meta def elabSpytialSpecCmd : CommandElab := fun
  | `(spytial_spec $id:ident [$ops,*]) => do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    liftTermElabM do
      let scope ← SelScope.ofType declName
      let spec ← elabSpytialOps scope ops.getElems
      setSpytialSpec declName spec
  | stx => throwError "Unexpected syntax {stx}."

/-- `spytial_ops <name> : <Type> [<ops>]` binds a named op list: a reusable
    spec fragment, elaborated here against `<Type>` as root. A `..<name>`
    element splices it into any op list with that same root — an attached
    `spytial_spec` or a use-site `with [...]`.

    The name is declared as an `SpytialOps` constant, so it takes the current
    namespace and is reached through `open`, `export` and aliases like any
    other declaration.

    ```
    spytial_ops quiet : Tree [hideAtom Nat]
    #spytial t with [..quiet, orientation left below]
    ```
-/
syntax (name := spytialOpsCmd) "spytial_ops " ident " : " ident " [" spytial_op,*,? "]" : command

@[command_elab spytialOpsCmd]
meta def elabSpytialOpsCmd : CommandElab := fun
  | `(spytial_ops $name:ident : $ty:ident [$ops,*]) => do
    let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ty
    -- a `module` file makes declarations private by default, and a list nobody
    -- downstream can splice is useless; the syntax has no visibility modifier
    let (declName, _) ← mkDeclName (← getCurrNamespace) { visibility := .public } name.getId
    let spec ← liftTermElabM do
      let scope ← SelScope.ofType root
      elabSpytialOps scope ops.getElems
    let declId := mkIdentFrom name (`_root_ ++ declName)
    elabCommand (← `(public meta def $declId : SpytialOps := .mk))
    liftCoreM <| setSpytialOps declName { root, ops := spec }
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
    let typeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo typeId
    let defName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo defId
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
syntax (name := spytialSpecDebug) "#spytial.spec " term " with " "[" spytial_op,*,? "]" : command

@[command_elab spytialSpecDebug]
meta def elabSpytialSpecDebug : CommandElab := fun
  | `(#spytial.spec $t:term with [$ops,*]) => do
    let specStr ← liftTermElabM do
      let e ← elabTermInstantiated t
      let spec ← elabUseSiteOps e ops.getElems
      -- The walk is only needed to resolve raw Lean selectors against the
      -- datum. A spec without one renders identically without it, and skipping
      -- it also skips asking each walked type for a `SpytialIdentity`.
      if spec.hasLeanRel then
        let (di, prov, evidence) ← relationalizeWithEvidence e
        return (← resolveLeanSelectors e di prov spec evidence).render
      else
        return spec.render
    logInfo m!"{specStr}"
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.datum <term>` prints the generated data instance as JSON.
    It shows the atoms and relations produced before any visualization and
    accepts the same observations as `#spytial`. -/
syntax (name := spytialDatumDebug) "#spytial.datum " term
  (" observing " "[" term,* "]")? : command

@[command_elab spytialDatumDebug]
meta def elabSpytialDatumDebug : CommandElab := fun stx => do
  let (_, _, di, _, _) ← liftTermElabM <| elabRelationalized stx[1] {} (optionalTerms stx[2])
  logInfo m!"{(toJson di).pretty}"

/-! ## Proof visualization -/

/-- `#spytial.proof <term>` visualizes a proof term without filtering Prop-typed fields.
    Unlike `#spytial` (data mode), this shows the full proof structure — sub-proofs,
    premises, and witnesses are all included as nodes and edges.

    Use `with [...]` to specify layout operations.
-/
syntax (name := spytialProofCmd) "#spytial.proof " term (" with " "[" spytial_op,*,? "]")? : command

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

/-- `#spytial.proof.datum <term>` prints the proof-mode data instance as JSON. -/
syntax (name := spytialProofDatumDebug) "#spytial.proof.datum " term : command

@[command_elab spytialProofDatumDebug]
meta def elabSpytialProofDatumDebug : CommandElab := fun
  | `(#spytial.proof.datum $t:term) => do
    let (_, _, di, _, _) ← liftTermElabM <| elabRelationalized t { filterProofs := false }
    logInfo m!"{(toJson di).pretty}"
  | stx => throwError "Unexpected syntax {stx}."

/-! ## IYKYK-backed tactic mode -/

private meta def resolveFyi (stx : Syntax) : TermElabM (Array Expr) := do
  if stx.getNumArgs == 0 then return #[]
  stx[2].getSepArgs.mapM fun rule => do
    let e ← elabTermInstantiated rule
    unless ← isProp (← inferType e) do
      throwErrorAt rule m!"'fyi' expects a hypothesis: a proof of a Prop-typed \
        statement, but this term has type {← inferType e}"
    return e

/-- Spytial's `wdyk` configuration. Simp is always enabled: it
    normalizes each fact before decomposition, so a constructor clash reduces
    to `False` (an inconsistent context) and a same-constructor equation
    splits into the field equalities that refine atoms. -/
private meta def contextConfig (hypotheses : Array Expr) : Iykyk.Config :=
  { hypotheses, mechanisms := #[.simp] }

/-- Extract knowledge with IYKYK and turn it into a Spytial widget payload. -/
private meta def spytialInContextProps? (subject : Expr)
    (ops? : Option (Array (TSyntax `spytial_op)) := none)
    (walkConfig : WalkConfig := {}) (hypotheses : Array Expr := #[])
    (observations : Array Expr := #[]) :
    TermElabM (Option Json × ContextViewStatus) := do
  let (status, view?) ←
    wdykInContext subject walkConfig (contextConfig hypotheses) observations
  let some view := view? | return (none, status)
  let spec? ← match ops? with
    | some ops => do
      let scope ← scopeForAfaik view.afaik (← scopeForExpr subject) observations
      let scope := if observations.isEmpty then scope
        else scopeWithObservedData scope view.data
      some <$> elabUseSiteOps subject ops (some scope)
    | none => lookupTypeSpec subject
  -- Both selector styles range over this datum. Lean predicates retain the
  -- represented terms and checked evidence instead of reading display labels.
  let spec? ← spec?.mapM fun s =>
    liftM (resolveLeanSelectors view.datum view.data view.prov s view.evidence)
  let props := spytialProps view.data (spec?.map SpytialSpec.render)
  return (some (props.setObjVal! "inspection" (toJson view.inspection)), status)

/-- Programmatic entry point for Spytial's IYKYK consumer. -/
public meta def spytialInContextProps (subject : Expr)
    (ops? : Option (Array (TSyntax `spytial_op)) := none)
    (walkConfig : WalkConfig := {}) (hypotheses : Array Expr := #[])
    (observations : Array Expr := #[]) :
    TermElabM (Json × ContextViewStatus) := do
  let (props?, status) ←
    spytialInContextProps? subject ops? walkConfig hypotheses observations
  let some props := props? | throwError "spytial: IYKYK found an inconsistent context"
  return (props, status)

open Tactic in
private meta def spytialInContextTac (term : Syntax)
    (observingSyntax fyiSyntax : Syntax)
    (ops? : Option (Array (TSyntax `spytial_op))) (invocation : Syntax) : TacticM Unit := do
  let (props?, status) ← withMainContext do
    let subject ← elabTermInstantiated term
    spytialInContextProps? subject ops? {} (← resolveFyi fyiSyntax)
      (← resolveObservations subject observingSyntax)
  if status.inconsistent then
    logWarning "spytial: IYKYK found an inconsistent context; no diagram rendered"
    return
  if status.truncated then
    logWarning "spytial: IYKYK reached an extraction limit; the diagram may be incomplete"
  let some props := props? | return
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) invocation

open Tactic in
/-- `spytial term` asks IYKYK what the current context establishes about
    `term`, translates that knowledge into relational data, and displays it.
    `observing [f₁, ...]` parameterizes that translation and displays each
    function over every compatible represented value; `fyi [h₁, ...]`
    supplies proved hypotheses or forward rules to IYKYK;
    `with [...]` supplies Spytial layout operations. -/
syntax (name := spytialTactic) "spytial " term (" observing " "[" term,* "]")?
  (" fyi " "[" term,* "]")?
  (" with " "[" spytial_op,*,? "]")? : tactic

open Tactic in
@[tactic spytialTactic]
meta def elabSpytialTactic : Tactic := fun stx =>
  spytialInContextTac stx[1] stx[2] stx[3] (optionalOps stx[4]) stx

meta def spytialDatumKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.datum" (includeIdent := true)

open Tactic in
/-- `spytial.datum term` prints Spytial's relational observation of the IYKYK
    result. It accepts the same observations and optional hypotheses as
    `spytial`. -/
syntax (name := spytialDatumTactic) spytialDatumKw term
  (" observing " "[" term,* "]")?
  (" fyi " "[" term,* "]")? : tactic

open Tactic in
@[tactic spytialDatumTactic]
meta def elabSpytialDatumTactic : Tactic := fun stx => withMainContext do
  let subject ← elabTermInstantiated stx[1]
  let observations ← resolveObservations subject stx[2]
  let (status, view?) ← wdykInContext subject {}
    (contextConfig (← resolveFyi stx[3])) observations
  if status.inconsistent then
    logWarning "spytial: IYKYK found an inconsistent context; no datum produced"
  else if let some view := view? then
    logInfo m!"{(toJson view.data).pretty}"
    if status.truncated then
      logWarning "spytial: IYKYK reached an extraction limit; the datum may be incomplete"


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
  (" with " "[" spytial_op,*,? "]")? : tactic

open Tactic in
@[tactic spytialProofTactic]
meta def elabSpytialProofTactic : Tactic := fun stx => do
  -- A quotation pattern would lex `spytial.proof` as one dotted ident and never
  -- match; extract positionally.
  let props ← withMainContext do
    spytialPayloadProps stx[1] (optionalOps stx[2]) { filterProofs := false }
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

end

end SpytialLean
