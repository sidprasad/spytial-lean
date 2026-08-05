module

public import Lean
public meta import SpytialLean.Selector
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Elab Meta

public section

/-! # SelectorElab — embedded selector syntax, checked against the data vocabulary

Selectors are written as Lean syntax (category `spytial_sel`) and elaborated
against a `SelScope`: the vocabulary of atoms and relations the relationalizer
can emit for values of the target type. Every identifier must resolve — to a
comprehension binder, a field relation, a type in the reachable closure, or (in
value position) a nullary constructor — and every operator's arity must make
sense, so a renamed cslib field or a typo'd sig is a compile error at the exact
ident, not a silently empty selection at render time.

Scopes are *strict* exactly when the vocabulary is closed: a monomorphic type
built from monomorphic fields. A type parameter, function-typed field, custom
relationalizer, or non-inductive in the closure opens the world — the walker can
then emit names no static analysis predicts — and unknown names downgrade to
warnings there.
-/

/-! ## Scope -/

/-- Everything the relationalizer can emit for values of the target type, per
    `TypeShape`. -/
meta structure SelScope where
  root : Name
  /-- Lean type name → sig string, over the reachable field-type closure. -/
  types : Std.HashMap Name String := {}
  /-- Relation name → the type whose constructor field emits it. -/
  rels : Std.HashMap String Name := {}
  /-- Nullary-constructor label → constructor, for `@:x = tt` literals. -/
  ctorLabels : Std.HashMap String Name := {}
  /-- Names introduced by earlier ops in the same spec (group names arity 1,
      inferred edges arity 2). -/
  introduced : Std.HashMap String Nat := {}
  /-- Open-world marker (see module docstring): unknown names become warnings. -/
  lenient : Bool := false
  deriving Inhabited

/-- Stop the closure walk where the walker stops decomposing. TODO: the walker
    still decomposes `Int`/`Char`/`UInt*` into constructor chains, so their
    closures must stay in the vocabulary until it treats them as scalars. -/
private meta def scalarTypes : List Name :=
  [``Nat, ``String, ``Float]

meta def SelScope.ofType (root : Name) : MetaM SelScope := do
  let env ← getEnv
  let mut scope : SelScope := { root }
  -- Stuck-match nodes can appear in any open value, typed at the scrutinized type.
  scope := { scope with rels := scope.rels.insert "scrutinee" root }
  let mut queue : Array Name := #[root]
  let mut seen : NameSet := {}
  while !queue.isEmpty do
    let t := queue.back!
    queue := queue.pop
    if seen.contains t then continue
    seen := seen.insert t
    scope := { scope with types := scope.types.insert t (shortName t) }
    -- a custom relationalizer's emissions are its own: the world is open past it
    if (getSpytialRelationalizerName? env t).isSome then
      scope := { scope with lenient := true }
      continue
    if scalarTypes.contains t then
      continue
    match ← TypeShape.ofInductive t with
    | none =>
      scope := { scope with lenient := true }
    | some ts =>
      for c in ts.ctors do
        if c.fields.isEmpty then
          scope := { scope with ctorLabels := scope.ctorLabels.insert c.ctorShort c.ctorName }
        for f in c.fields do
          unless f.isProofLike do
            scope := { scope with rels := scope.rels.insert f.relName t }
            match f.typeHead with
            | some ft => queue := queue.push ft
            | none => scope := { scope with lenient := true }
  return scope

meta def SelScope.introduce (scope : SelScope) (name : String) (arity : Nat) : SelScope :=
  { scope with introduced := scope.introduced.insert name arity }

/-! ## Diagnostics -/

private meta def editDistance (a b : String) : Nat := Id.run do
  let s := a.toList.toArray
  let t := b.toList.toArray
  let mut prev := Array.range (t.size + 1)
  for i in [1:s.size + 1] do
    let mut curr := Array.replicate (t.size + 1) 0 |>.set! 0 i
    for j in [1:t.size + 1] do
      let cost := if s[i-1]! == t[j-1]! then 0 else 1
      curr := curr.set! j (min (min (prev[j]! + 1) (curr[j-1]! + 1)) (prev[j-1]! + cost))
    prev := curr
  return prev[t.size]!

private meta def sortDedup (xs : Array String) : Array String :=
  xs.qsort (· < ·) |>.foldl (init := #[]) fun acc s =>
    if acc.back? == some s then acc else acc.push s

private meta def SelScope.vocabulary (scope : SelScope) : Array String := Id.run do
  let mut out : Array String := #[]
  for (r, _) in scope.rels do out := out.push r
  for (_, s) in scope.types do out := out.push s
  for (n, _) in scope.introduced do out := out.push n
  return sortDedup out

private meta def suggest (scope : SelScope) (unknown : String) : String :=
  let vocab := scope.vocabulary
  let near := vocab.filter (fun v => editDistance unknown v ≤ 2)
  if !near.isEmpty then
    s!" (did you mean {", ".intercalate (near.toList.map (fun v => s!"'{v}'"))}?)"
  else if vocab.size ≤ 24 then
    s!"; vocabulary of '{scope.root}': {", ".intercalate vocab.toList}"
  else
    ""

/-- `U+XXXX` spelling, for a character with no printable form. -/
private meta def codepoint (c : Char) : String :=
  s!"U+{String.ofList ((Nat.toDigits 16 c.val.toNat).leftpad 4 '0') |>.toUpper}"

/-- Error in strict scopes, warning in lenient ones (the walker may emit names
    we cannot predict). Returns `recovery` when lenient. -/
private meta def unknownName {α} (scope : SelScope) (ref : Syntax) (what : String)
    (recovery : α) : TermElabM α := do
  let msg := m!"unknown {what}{suggest scope ref.getId.toString}"
  if scope.lenient then
    logWarningAt ref (msg ++ m!" — the vocabulary of '{scope.root}' is open (a \
      custom relationalizer, type parameter, or function field makes it \
      unpredictable), so the name passes through unchecked")
    return recovery
  else
    throwErrorAt ref msg

/-! ## Syntax -/

declare_syntax_cat spytial_sel
declare_syntax_cat spytial_sel_form
declare_syntax_cat spytial_sel_val
declare_syntax_cat spytial_sel_cmparg

/-- Binder group of a set comprehension: `x, y : BDD`. -/
syntax spytialSelBinderGroup := sepBy1(ident, ", ") " : " spytial_sel

syntax:100 (name := selIdent) ident : spytial_sel
syntax:100 "(" spytial_sel ")" : spytial_sel
syntax:100 "{" sepBy1(spytialSelBinderGroup, ", ") " | " spytial_sel_form "}" : spytial_sel
/-- Escape hatch: a string literal in selector position is a verbatim,
    unchecked SGQ expression. -/
-- TODO: close the remaining grammar gaps so the escape hatch is rarely needed —
-- `#` (cardinality), `<:`/`:>` (domain/range restriction), box join, and `let`
-- are not yet surfaced.
syntax:100 (name := selStr) str : spytial_sel
syntax:30 spytial_sel:30 " + " spytial_sel:31 : spytial_sel
syntax:30 spytial_sel:30 " - " spytial_sel:31 : spytial_sel
syntax:40 spytial_sel:40 " & " spytial_sel:41 : spytial_sel
syntax:50 spytial_sel:50 " -> " spytial_sel:51 : spytial_sel
syntax:60 spytial_sel:60 " . " spytial_sel:61 : spytial_sel
syntax:70 "^" spytial_sel:70 : spytial_sel
syntax:70 "*" spytial_sel:70 : spytial_sel
syntax:70 "~" spytial_sel:70 : spytial_sel

syntax "@:" spytial_sel:100 : spytial_sel_val
syntax "@str:" spytial_sel:100 : spytial_sel_val
syntax "@bool:" spytial_sel:100 : spytial_sel_val
syntax "@num:" spytial_sel:100 : spytial_sel_val
syntax str : spytial_sel_val
syntax num : spytial_sel_val

syntax (priority := high) spytial_sel_val : spytial_sel_cmparg
syntax spytial_sel : spytial_sel_cmparg

syntax:50 spytial_sel_cmparg " = " spytial_sel_cmparg : spytial_sel_form
syntax:50 spytial_sel_cmparg " != " spytial_sel_cmparg : spytial_sel_form
syntax:50 spytial_sel " in " spytial_sel : spytial_sel_form
-- Forge's symbolic connective spellings (`&&`/`||`/`=>`/`!` alias
-- `and`/`or`/`implies`/`not`). The word forms cannot be parsed here: they would
-- need non-reserved keywords, which lose dispatch to the bare-ident rule, and
-- reserving them would break `.and`-style dot idents everywhere else. Lowering
-- still emits the word forms.
syntax:35 spytial_sel_form:35 " && " spytial_sel_form:36 : spytial_sel_form
syntax:25 spytial_sel_form:25 " || " spytial_sel_form:26 : spytial_sel_form
syntax:15 spytial_sel_form:16 " => " spytial_sel_form:15 : spytial_sel_form
syntax:45 "!" spytial_sel_form:45 : spytial_sel_form
syntax:100 "(" spytial_sel_form ")" : spytial_sel_form
-- Multiplicity formulas (Forge): `some`/`no`/`lone`/`one <sel>`. Prefix, at
-- atomic-formula precedence so they bind tighter than `&&`/`||`/`=>`. Parsed as
-- a leading ident — the keywords cannot be reserved tokens without shadowing
-- ordinary identifiers like `Option.some` — and dispatched in `elabForm`, where
-- a non-keyword head errors; the comparison forms keep their `=`/`!=`/`in`.
syntax:50 (name := selMult) ident spytial_sel : spytial_sel_form

/-! ## Elaboration

Elaboration returns the reified selector and its arity; `none` arity means
statically unknown (`raw`, or an unknown name passed through leniently), which
soft-disables downstream arity requirements. -/

private meta def checkArity (ref : Syntax) (what : String) (got : Option Nat)
    (want : Nat) : TermElabM Unit := do
  if let some got := got then
    unless got == want do
      throwErrorAt ref m!"{what} must have arity {want}, got {got}"

private meta def joinArity (ref : Syntax) : Option Nat → Option Nat → TermElabM (Option Nat)
  | some a, some b => do
    if a + b < 3 then
      throwErrorAt ref m!"join of arity {a} and arity {b} has no columns left"
    return some (a + b - 2)
  | _, _ => return none

private meta def sameArity (ref : Syntax) (op : String) :
    Option Nat → Option Nat → TermElabM (Option Nat)
  | some a, some b => do
    unless a == b do
      throwErrorAt ref m!"operands of {op} must have equal arity, got {a} and {b}"
    return some a
  | some a, none | none, some a => return some a
  | none, none => return none

/-- Resolve an ident as a global constant, quietly returning `none` when it
    does not resolve (with hover/go-to-def info when it does). -/
private meta def resolveGlobal? (stx : Syntax) : TermElabM (Option Name) := do
  try
    pure (some (← realizeGlobalConstNoOverloadWithInfo stx))
  catch _ =>
    pure none

/-- Resolve an identifier in relational position. Multi-component idents
    (`x.v` lexes as one ident) are join chains — unless the whole name resolves
    as a type reference (`Cslib.SKI`): the head resolves like a bare name,
    every later component must be a relation. -/
private meta def resolveSelIdent (scope : SelScope) (vars : List Name)
    (stx : Syntax) : TermElabM (Sel × Option Nat) := do
  match stx.getId.components with
  | [] => throwErrorAt stx "empty selector name"
  | head :: rest => do
    if !rest.isEmpty && !vars.contains head then
      if let some res ← resolveTypeRef? stx then
        return res
    let init ← resolveHead head
    rest.foldlM (init := init) fun (sel, arity) comp => do
      let compStr := comp.toString
      if scope.rels.contains compStr || scope.introduced.contains compStr then
        return (.join sel (.rel compStr), ← joinArity stx arity (some 2))
      else
        unknownName scope stx s!"relation '{compStr}'" (Sel.join sel (.rel compStr), none)
where
  /-- An ident as a sig reference to a known (or leniently unknown) type. -/
  resolveTypeRef? (idStx : Syntax) : TermElabM (Option (Sel × Option Nat)) := do
    let some constName ← resolveGlobal? idStx | return none
    match (← getEnv).find? constName with
    | some (.inductInfo _) =>
      if scope.types.contains constName then
        return some (.sig constName (shortName constName), some 1)
      else if scope.lenient then
        -- An open world cannot rule the type out, and referencing an element
        -- type of a polymorphic container is the normal case — pass silently.
        return some (.sig constName (shortName constName), some 1)
      else
        throwErrorAt stx m!"type '{constName}' cannot occur in values of \
          '{scope.root}'{suggest scope (shortName constName)}"
    | some (.ctorInfo _) =>
      throwErrorAt stx m!"'{constName}' is a constructor — constructor literals \
        only occur in label comparisons (e.g. `@:x = {shortName constName}`)"
    | _ => return none
  resolveHead (head : Name) : TermElabM (Sel × Option Nat) := do
    let s := head.toString
    if vars.contains head then
      return (.var head, some 1)
    if s == "univ" then return (.univ, some 1)
    if s == "iden" then return (.iden, some 2)
    if scope.rels.contains s then
      return (.rel s, some 2)
    if let some arity := scope.introduced.get? s then
      return (.rel s, some arity)
    -- Not a relation: a sig is a real Lean type reference.
    if let some res ← resolveTypeRef? (mkIdentFrom stx head) then
      return res
    unknownName scope stx s!"name '{s}'" (Sel.rel s, none)

/-- Resolve a bare identifier in value position: a nullary constructor whose
    short name is the atom label the walker emits. Unqualified labels resolve
    through the scope (`tt` means `BDD.tt` without any `open`), qualified ones
    through the Lean resolver. -/
private meta def resolveCtorLit (scope : SelScope) (stx : Syntax) : TermElabM SelVal := do
  if let some ctorName := scope.ctorLabels.get? stx.getId.toString then
    if let some e ← try pure (some (← mkConstWithLevelParams ctorName)) catch _ => pure none then
      discard <| Term.addTermInfo stx e
    return .ctorLit ctorName (shortName ctorName)
  let some constName ← resolveGlobal? stx
    | throwErrorAt stx m!"unknown constructor label '{stx.getId}'; known labels of \
        '{scope.root}': {", ".intercalate (sortDedup (scope.ctorLabels.toList.map (·.1)).toArray).toList}"
  match (← getEnv).find? constName with
  | some (.ctorInfo ci) =>
    unless ci.numFields == 0 do
      throwErrorAt stx m!"'{constName}' has fields — only nullary constructors \
        are atom labels"
    if !scope.types.contains ci.induct && !scope.lenient then
      throwErrorAt stx m!"constructor '{constName}' belongs to '{ci.induct}', \
        which cannot occur in values of '{scope.root}'"
    return .ctorLit constName (shortName constName)
  | _ =>
    throwErrorAt stx m!"'{constName}' is not a constructor; label comparisons \
      expect a nullary constructor or a literal"

/-- The value form inside a comparison argument, if it is one. -/
private meta def cmpVal? (arg : TSyntax `spytial_sel_cmparg) : Option Syntax :=
  match arg with
  | `(spytial_sel_cmparg| $v:spytial_sel_val) => some v
  | _ => none

/-- The relational form inside a comparison argument. -/
private meta def cmpSel! (arg : TSyntax `spytial_sel_cmparg) : TSyntax `spytial_sel :=
  match arg with
  | `(spytial_sel_cmparg| $s:spytial_sel) => s
  | _ => ⟨arg.raw⟩

/-- A relational expression opposite a value: only a bare ident makes sense, as
    a constructor-label literal. -/
private meta def coerceVal (scope : SelScope) (arg : TSyntax `spytial_sel_cmparg) :
    TermElabM SelVal := do
  match cmpSel! arg with
  | `(spytial_sel| $x:ident) => resolveCtorLit scope x
  | s => throwErrorAt s "cannot compare a label value with a relational \
      expression; project a label with `@:` or compare against a constructor \
      or literal"

mutual

private meta partial def elabSel (scope : SelScope) (vars : List Name) :
    Syntax → TermElabM (Sel × Option Nat)
  | `(spytial_sel| $x:ident) =>
    resolveSelIdent scope vars x
  | `(spytial_sel| ($s)) => elabSel scope vars s
  | `(spytial_sel| $s:str) => return (.raw s.getString, none)
  | stx@`(spytial_sel| $a + $b) => elabBinary scope vars stx .union "+" a b
  | stx@`(spytial_sel| $a - $b) => elabBinary scope vars stx .diff "-" a b
  | stx@`(spytial_sel| $a & $b) => elabBinary scope vars stx .inter "&" a b
  | `(spytial_sel| $a -> $b) => do
    let (sa, aa) ← elabSel scope vars a
    let (sb, ab) ← elabSel scope vars b
    let arity : Option Nat := do return (← aa) + (← ab)
    return (.prod sa sb, arity)
  | stx@`(spytial_sel| $a . $b) => do
    let (sa, aa) ← elabSel scope vars a
    let (sb, ab) ← elabSel scope vars b
    return (.join sa sb, ← joinArity stx aa ab)
  | stx@`(spytial_sel| ^$a) => elabClosure scope vars stx .trans "^" a
  | stx@`(spytial_sel| *$a) => elabClosure scope vars stx .reflTrans "*" a
  | stx@`(spytial_sel| ~$a) => elabClosure scope vars stx .transpose "~" a
  | `(spytial_sel| {$groups,* | $body}) => do
    let mut binders : Array (Name × Sel) := #[]
    let mut vars := vars
    for group in groups.getElems do
      match group with
      | `(spytialSelBinderGroup| $xs,* : $dom) => do
        let (domSel, domArity) ← elabSel scope vars dom
        checkArity dom "a comprehension binder domain" domArity 1
        for x in xs.getElems do
          binders := binders.push (x.getId, domSel)
          vars := x.getId :: vars
      | g => throwErrorAt g "unexpected binder group"
    let bodyForm ← elabForm scope vars body
    return (.compr binders bodyForm, some binders.size)
  | stx => throwErrorAt stx "unexpected selector syntax"

private meta partial def elabBinary (scope : SelScope) (vars : List Name) (stx : Syntax)
    (mk : Sel → Sel → Sel) (op : String) (a b : TSyntax `spytial_sel) :
    TermElabM (Sel × Option Nat) := do
  let (sa, aa) ← elabSel scope vars a
  let (sb, ab) ← elabSel scope vars b
  return (mk sa sb, ← sameArity stx op aa ab)

private meta partial def elabClosure (scope : SelScope) (vars : List Name) (stx : Syntax)
    (mk : Sel → Sel) (op : String) (a : TSyntax `spytial_sel) :
    TermElabM (Sel × Option Nat) := do
  let (sa, aa) ← elabSel scope vars a
  checkArity stx s!"the operand of {op}" aa 2
  return (mk sa, some 2)

/-- Elaborate a value operand (`@:`-projection or literal). -/
private meta partial def elabVal (scope : SelScope) (vars : List Name) :
    Syntax → TermElabM SelVal
  | stx@`(spytial_sel_val| @:$e) => elabLabel scope vars stx .plain e
  | stx@`(spytial_sel_val| @str:$e) => elabLabel scope vars stx .str e
  | stx@`(spytial_sel_val| @bool:$e) => elabLabel scope vars stx .bool e
  | stx@`(spytial_sel_val| @num:$e) => elabLabel scope vars stx .num e
  | `(spytial_sel_val| $s:str) => do
    if let some c := sgqUnspellableChar? s.getString then
      throwErrorAt s m!"string literal contains {codepoint c} — SGQ's string \
        syntax has no escape for it, and it cannot ride raw through the spec"
    return .strLit s.getString
  | `(spytial_sel_val| $n:num) => return .numLit n.getNat
  | stx => throwErrorAt stx "unexpected value syntax"

private meta partial def elabLabel (scope : SelScope) (vars : List Name) (stx : Syntax)
    (proj : LabelProj) (e : TSyntax `spytial_sel) : TermElabM SelVal := do
  let (sel, arity) ← elabSel scope vars e
  checkArity stx "a label projection's operand" arity 1
  return .label proj sel

/-- Elaborate a comparison: value-vs-value when either side is a value form
    (a bare ident opposite a value is a constructor literal), else relational. -/
private meta partial def elabCmp (scope : SelScope) (vars : List Name) (stx : Syntax)
    (neg : Bool) (a b : TSyntax `spytial_sel_cmparg) : TermElabM SelForm := do
  let mkV (va vb : SelVal) : SelForm := if neg then .vneq va vb else .veq va vb
  match cmpVal? a, cmpVal? b with
  | some va, some vb =>
    return mkV (← elabVal scope vars va) (← elabVal scope vars vb)
  | some va, none =>
    return mkV (← elabVal scope vars va) (← coerceVal scope b)
  | none, some vb =>
    return mkV (← coerceVal scope a) (← elabVal scope vars vb)
  | none, none => do
    let (sa, aa) ← elabSel scope vars (cmpSel! a)
    let (sb, ab) ← elabSel scope vars (cmpSel! b)
    discard <| sameArity stx (if neg then "!=" else "=") aa ab
    return if neg then .neq sa sb else .eq sa sb

private meta partial def elabForm (scope : SelScope) (vars : List Name) :
    Syntax → TermElabM SelForm
  | stx@`(spytial_sel_form| $a:spytial_sel_cmparg = $b) => elabCmp scope vars stx false a b
  | stx@`(spytial_sel_form| $a:spytial_sel_cmparg != $b) => elabCmp scope vars stx true a b
  | stx@`(spytial_sel_form| $a:spytial_sel in $b) => do
    let (sa, aa) ← elabSel scope vars a
    let (sb, ab) ← elabSel scope vars b
    discard <| sameArity stx "in" aa ab
    return .subset sa sb
  | `(spytial_sel_form| $a && $b) =>
    return .and (← elabForm scope vars a) (← elabForm scope vars b)
  | `(spytial_sel_form| $a || $b) =>
    return .or (← elabForm scope vars a) (← elabForm scope vars b)
  | `(spytial_sel_form| $a => $b) =>
    return .implies (← elabForm scope vars a) (← elabForm scope vars b)
  | `(spytial_sel_form| !$a) => return .not (← elabForm scope vars a)
  | `(spytial_sel_form| ($f)) => elabForm scope vars f
  -- Multiplicity (`some`/`no`/`lone`/`one`): any arity, so the operand is only
  -- scope-checked; the head keyword is validated first.
  | `(spytial_sel_form| $kw:ident $a:spytial_sel) => do
    let mk ← match kw.getId.toString with
      | "some" => pure SelForm.some_
      | "no" => pure SelForm.no
      | "lone" => pure SelForm.lone
      | "one" => pure SelForm.one
      | other => throwErrorAt kw m!"unknown multiplicity operator '{other}' \
          (expected some, no, lone, one)"
    return mk (← elabSel scope vars a).1
  | stx => throwErrorAt stx "unexpected formula syntax"

end

/-! ## Entry points -/

/-- `pair` positions project first/last at runtime, so a wider selector warns
    rather than errors. -/
meta inductive ArityExpect where
  | unary
  | pair
  | unaryOrPair
  deriving Repr, Inhabited

/-- Elaborate a selector against `scope`, enforcing the op position's arity
    expectation (skipped when the arity is statically unknown). -/
meta def elabSelector (scope : SelScope) (expect : ArityExpect)
    (stx : TSyntax `spytial_sel) : TermElabM Sel := do
  let (sel, arity) ← elabSel scope [] stx
  if let some a := arity then
    match expect with
    | .unary =>
      unless a == 1 do
        throwErrorAt stx m!"this position selects atoms (arity 1), but the \
          selector has arity {a}"
    | .pair =>
      if a < 2 then
        throwErrorAt stx m!"this position selects pairs (arity 2), but the \
          selector has arity {a}"
      else if a > 2 then
        logWarningAt stx m!"arity-{a} selector in a pair position: only the \
          first and last columns of each tuple are used"
    | .unaryOrPair =>
      unless a == 1 || a == 2 do
        throwErrorAt stx m!"this position selects atoms or pairs (arity 1 or \
          2), but the selector has arity {a}"
  return sel

meta def elabFieldName (scope : SelScope) (stx : TSyntax `ident) : TermElabM String := do
  let s := stx.getId.toString
  if scope.rels.contains s || scope.introduced.contains s then
    return s
  unknownName scope stx s!"relation '{s}'" s

end

end SpytialLean
