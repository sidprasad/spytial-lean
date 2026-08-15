module

public import Lean
public meta import SpytialLean.TypeShape

namespace SpytialLean

open Lean Meta Elab

/-! # Declared identity for the Spytial relationalizer

`SpytialIdentity` declares, per type, which occurrences of a value merge into
one atom: every value gets an identity; subterms with the same identity are one
atom. No instance ⇒ no merging — the term draws as written. This module is the
value layer only: the identity token, the encoding class (`ToIdentityKey`), the
two presentations, the identity class, the `deriving` handler for structural
identity, and the `Raw`/`Viewed` view wrappers. The walker (`Relationalizer`)
consumes these. -/

/-! ## IdentityKey -/

/-- Internal representation of `IdentityKey`. Leaves (`str`, `nat`) and
    composites (`node`) are distinct constructors, so tupling is injective for
    free. `spelling` is its own constructor so the walker's opacity gate
    (keying a deliberately-opaque leaf by its spelling) can never collide with
    a genuine structural or encoded key. -/
private inductive KeyRep where
  | str (s : String)
  | nat (n : Nat)
  | node (ks : List KeyRep)
  | spelling (s : String)
  deriving BEq, Hashable, Repr, Inhabited

/-- Opaque identity token. Guaranteed properties: decidable equality, hashable,
    and injective tupling from string/number leaves — `ofList [ofString "leaf",
    ofNat 1]` can never encode the same token as `ofString "leaf1"`. Construct
    only via `ofString`, `ofNat`, `ofList`; the representation (e.g. internal
    interning) is free to change. -/
public structure IdentityKey where
  private rep : KeyRep
  deriving BEq, Hashable, Repr, Inhabited

public def IdentityKey.ofString (s : String) : IdentityKey := ⟨.str s⟩

public def IdentityKey.ofNat (n : Nat) : IdentityKey := ⟨.nat n⟩

public def IdentityKey.ofList (ks : List IdentityKey) : IdentityKey :=
  ⟨.node (ks.map (·.rep))⟩

/-- Key for a deliberately-opaque leaf (`@[irreducible]` / `opaque` head), from
    its spelling — the walker's opacity gate. A distinct constructor underneath,
    so a spelling key never collides with any `ofString`/`ofNat`/`ofList` key a
    structural or encoded identity can produce: `leaf hidden` merges with other
    occurrences of the same spelling and with nothing else. -/
public def IdentityKey.ofSpelling (s : String) : IdentityKey := ⟨.spelling s⟩

/-! ## Encoding: ToIdentityKey

Encoding is not identity: writing a value into a key and merging that value's
atoms are two different judgments about a type, so they are two classes.
Deriving over a `Nat` field writes the field's value into the parent's key via
`ToIdentityKey` — without ever making `Nat` atoms merge. -/

/-- Values of `α` can be written into a key; grants NO merge behavior.
    (`SpytialIdentity` remains purely the merge declaration — no primitive has
    one by default; the ruled as-written default stands, literals included.)
    `toKey` must be injective — distinct values, distinct keys — so parent
    identities built from it never conflate fields. -/
public class ToIdentityKey (α : Type u) where
  /-- Encode a value as a key. -/
  toKey : α → IdentityKey

public instance : ToIdentityKey Nat where
  toKey := .ofNat

public instance : ToIdentityKey String where
  toKey := .ofString

public instance : ToIdentityKey Bool where
  toKey b := .ofNat b.toNat

public instance : ToIdentityKey Char where
  toKey c := .ofNat c.toNat

public instance : ToIdentityKey Int where
  toKey
    | .ofNat n => .ofList [.ofString "ofNat", .ofNat n]
    | .negSucc n => .ofList [.ofString "negSucc", .ofNat n]

public instance : ToIdentityKey UInt8 where
  toKey n := .ofNat n.toNat

public instance : ToIdentityKey UInt16 where
  toKey n := .ofNat n.toNat

public instance : ToIdentityKey UInt32 where
  toKey n := .ofNat n.toNat

public instance : ToIdentityKey UInt64 where
  toKey n := .ofNat n.toNat

public instance : ToIdentityKey USize where
  toKey n := .ofNat n.toNat

/-! Container lifts. Each tags its shape (`"list"`, `"some"`, …), so injective
tupling is preserved compositionally — every encoding is a tagged node in a
free algebra, so distinct arms never collide and equal encodings force equal
components: `some []` and `none` in `Option (List α)` can never encode alike. -/

public instance {α : Type u} [ToIdentityKey α] : ToIdentityKey (List α) where
  toKey xs := .ofList (.ofString "list" :: xs.map ToIdentityKey.toKey)

public instance {α : Type u} [ToIdentityKey α] : ToIdentityKey (Array α) where
  toKey xs := .ofList (.ofString "array" :: (xs.map ToIdentityKey.toKey).toList)

public instance {α : Type u} [ToIdentityKey α] : ToIdentityKey (Option α) where
  toKey
    | none => .ofList [.ofString "none"]
    | some a => .ofList [.ofString "some", ToIdentityKey.toKey a]

public instance {α : Type u} {β : Type v} [ToIdentityKey α] [ToIdentityKey β] :
    ToIdentityKey (α × β) where
  toKey p := .ofList [.ofString "prod", ToIdentityKey.toKey p.1, ToIdentityKey.toKey p.2]

/-! ## Presentations -/

/-- How a type presents its identity: as a classifier or as a decider. -/
public inductive IdentityVia (α : Type u) where
  /-- Classifier: one computation per subterm, table lookup to merge. -/
  | identity (f : α → IdentityKey)
  /-- Decider: reuse your equality, e.g. `(· == ·)`. Must be an equivalence
      relation — reflexive, symmetric, transitive. (Deliberately not
      `LawfulBEq`, which demands agreement with `=` and would outlaw exactly
      the coarser-than-structural quotients this design exists for.) Cost: up
      to one comparison per existing group of the type — linear in the group
      count, worst case — vs one lookup. -/
  | eqv (r : α → α → Bool)

/-- The classifier, when this presentation has one. Derived instances dispatch
    on this to decide whether a composite can stay classifier-presented. -/
public def IdentityVia.classifier? {α : Type u} : IdentityVia α → Option (α → IdentityKey)
  | .identity f => some f
  | .eqv _ => none

/-- Every presentation induces a decider — classifiers compare by key. (The
    reverse direction, a classifier from a decider, does not exist; that
    asymmetry is why derived instances degrade to `eqv` when any ingredient
    is decider-presented.) -/
public def IdentityVia.toEqv {α : Type u} : IdentityVia α → (α → α → Bool)
  | .identity f => fun a b => f a == f b
  | .eqv r => r

/-- Pull a presentation back along a function: identify `a` with `b` iff `v`
    identifies `n a` with `n b`. Classifiers stay classifiers. -/
public def IdentityVia.comap {α : Type u} {β : Type v} (v : IdentityVia β) (n : α → β) :
    IdentityVia α :=
  match v with
  | .identity f => .identity (f ∘ n)
  | .eqv r => .eqv fun a b => r (n a) (n b)

/-! ## The class -/

/-- Declared diagram identity for `α`: subterms of type `α` with the same
    identity merge into one atom. No instance ⇒ no merging — the term draws as
    written, and no primitive ships an instance (writing a value into a parent
    key is `ToIdentityKey`'s job and grants no merging). `deriving
    SpytialIdentity` gives the structural identity, which fits value-like
    domains (sameness is same content); syntax-like domains, where position is
    meaning, should simply not opt in. -/
public class SpytialIdentity (α : Type u) where
  /-- Which occurrences are one atom. -/
  via : IdentityVia α
  /-- Display layer: the drawn representative of each identity class. Law:
      `identity (norm x) = identity x` — normalizing must not change identity;
      the representative is a member of the class it represents. Under
      structural identity the choice is invisible; it matters exactly when
      identity is coarser than structural. -/
  norm? : Option (α → α) := none

/-- The `via` of `α`'s instance with `α` explicit — the form generated code and
    dispatch sites use. -/
public def SpytialIdentity.viaOf (α : Type u) [inst : SpytialIdentity α] : IdentityVia α :=
  inst.via

/-- Reuse the type's `BEq` as the decider presentation: `.eqv (· == ·)`.
    The instance must be a genuine equivalence relation (see `IdentityVia.eqv`);
    writing this is the declaration that it is — `BEq`-existence alone never
    triggers merging. -/
@[reducible] public def SpytialIdentity.ofBEq {α : Type u} [BEq α] : SpytialIdentity α :=
  { via := .eqv (· == ·) }

/-- The common "normalize, then use the underlying identity" quotient in one
    line: `base` pulled back along `n`, with `n` recorded as the display
    representative. The `norm?` law holds exactly when `n` is idempotent —
    which is what makes it a normalizer. For a type with a derived structural
    instance, `ofNorm n (SpytialIdentity.viaOf T)` is the doc's
    "`structuralIdentity ∘ n`" pairing. -/
@[reducible] public def SpytialIdentity.ofNorm {α : Type u} (n : α → α) (base : IdentityVia α) :
    SpytialIdentity α :=
  { via := base.comap n, norm? := some n }

/-! ## Views: Raw and Viewed

The walk carries an ambient mode — `declared` (consult `SpytialIdentity`,
absent ⇒ fresh atom) or `asWritten` (no instance consultation, fresh atoms) —
and these wrappers shift it for a subtree: quasiquote and unquote, for
diagrams (the doc's walk-modes table). Mode semantics live in the walker; this
layer provides only the types. -/

/-- `α` under a different name — the `OrderDual` device. `Raw.mk t` shifts the
    walk mode to `asWritten` for its whole subtree — hereditary by meaning,
    since "as written" is a property of a whole term — the quasiquote row of
    the doc's walk-modes table. `Raw α` is a different type head, so instance
    search finds no `SpytialIdentity` for it; the walker unwraps the wrapper on
    sight, so no wrapper atom appears. Deliberately a semireducible `def`:
    typeclass search runs at reducible transparency and cannot see through it
    (pinned by test). Instances declared directly on `Raw τ` are found as
    usual. -/
@[expose] public def Raw (α : Type u) : Type u := α

-- `@[expose]` on the `mk`s too: without it, module contexts cannot whnf-melt
-- the wrapper application, and the walker's unwrap relies on the melt.
@[expose] public def Raw.mk {α : Type u} (a : α) : Raw α := a

/-- The dual shift: `Viewed.mk t` returns the walk mode to `declared` for its
    subtree — the unquote — so a term can be drawn as written *except* one
    collapsed sub-region (the doc's walk-modes table). Same `OrderDual` device
    and instance-search invisibility as `Raw`; mode semantics live in the
    walker. -/
@[expose] public def Viewed (α : Type u) : Type u := α

@[expose] public def Viewed.mk {α : Type u} (a : α) : Viewed α := a

/-! ## Derived-structural registry

The deriving handler records each type it derives, so the walker can recognize
"this type's instance is the derived structural one" and compute identities
meta-side during the walk, without `evalExpr`. -/

/-- Environment extension recording types whose `SpytialIdentity` instance is
    the derived structural one. -/
public meta initialize spytialStructuralExt :
    SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun arrays =>
      arrays.foldl (fun s arr => arr.foldl (·.insert ·) s) {}
  }

/-- Whether `typeName`'s `SpytialIdentity` instance is the derived structural
    one. -/
public meta def isSpytialStructural (env : Environment) (typeName : Name) : Bool :=
  spytialStructuralExt.getState env |>.contains typeName

/-! ## Deriving handler

Generates, per inductive: a structural key function (classifier), a structural
comparison function (decider), and an instance. The field rule: a dependency
routes through its `SpytialIdentity` when an instance is declared — identity-
respecting composition wins — else through its `ToIdentityKey` (a total
classifier), else the deriving fails with the ordinary instance-synthesis
error. Parameter-dependent dependencies always route through `SpytialIdentity`
(the instance binds `[SpytialIdentity α]`): containers merge iff their
elements do. Presentations propagate: classifier-presented when every
identity-routed dependency has a classifier, degraded to the decider otherwise
(`List α` is classifier-presented iff `α` is); encoded dependencies never
force degradation. -/

namespace Identity

open Lean.Elab.Deriving Lean.Parser.Term Command

/-- How a dependency's key/decider reach the generated code — the field rule's
    verdict. -/
private meta inductive DepPath where
  /-- Consult `SpytialIdentity depTy`: runtime dispatch on its presentation,
      with degraded-`.eqv` propagation. Always the route for parameter-
      dependent types. -/
  | identity
  /-- `ToIdentityKey depTy`: encoding only, a total classifier. -/
  | encoding
  deriving Inhabited

/-- A non-recursive, non-parameter field type the generated code needs an
    identity for: its canonical form (parameters abstracted) for dedup, its
    rendering against the shared binder names, the binder idents the aux
    functions take its classifier/decider through, and the field rule's
    verdict (resolved in a post-pass over the deriving site's instances).
    Parameters are `Dep`s too — their `canon` is a loose bvar. -/
private meta structure Dep where
  canon : Expr
  type : Term
  keyId : Ident
  eqvId : Ident
  path : DepPath := .identity
  deriving Inhabited

private meta inductive FieldKind where
  | proofLike
  | recursive (memberIdx : Nat)
  | dep (depIdx : Nat)

private meta structure CtorPlan where
  ctorName : Name
  tag : String
  numParams : Nat
  kinds : Array FieldKind

private meta structure MemberPlan where
  indVal : InductiveVal
  ctorPlans : Array CtorPlan

private meta structure DerivCtx where
  argNames : Array Name
  members : Array MemberPlan
  deps : Array Dep
  keyFnNames : Array Name
  eqvFnNames : Array Name
  usePartial : Bool

private meta def unsupported (declName : Name) (msg : MessageData) : TermElabM α :=
  throwError "cannot derive `SpytialIdentity` for `{.ofConstName declName}`: {msg}"

/-- Render a field type as syntax the generated code can mention: constants,
    applications, literals, and the inductive's parameters (as their shared
    binder names). Anything else — function types, dependencies on sibling
    fields — has no structural identity and is rejected. -/
private meta partial def renderDepType (declName : Name) (paramIds : Array (FVarId × Ident)) :
    Expr → TermElabM Term
  | .fvar id =>
    match paramIds.findSome? (fun (fv, x) => if fv == id then some x else none) with
    | some x => pure x
    | none => unsupported declName
        m!"a field type depends on a sibling field, which structural identity cannot key"
  | .const c _ => `(@$(mkCIdent c):ident)
  | .lit (.natVal n) => pure (quote n)
  | .lit (.strVal s) => pure (quote s)
  | e@(.app ..) => do
    let args ← e.getAppArgs.mapM (renderDepType declName paramIds)
    match e.getAppFn with
    | .const c _ => `(@$(mkCIdent c):ident $args:term*)
    | .fvar id => do
      let fn ← renderDepType declName paramIds (.fvar id)
      `($fn $args:term*)
    | fn => unsupported declName m!"unsupported field type head{indentExpr fn}"
  | e => unsupported declName m!"unsupported field type{indentExpr e}"

/-- The field rule, resolved against the deriving site's instances:
    `SpytialIdentity` when declared, else `ToIdentityKey`, else the ordinary
    instance-synthesis error (thrown by the final `synthInstance`). Parameter-
    dependent dependencies (loose bvars in `canon`) are not synthesizable here
    and always route through `SpytialIdentity` — the generated instance binds
    `[SpytialIdentity α]`, so containers merge iff their elements do. -/
private meta def depPath (canon : Expr) : TermElabM DepPath := do
  if canon.hasLooseBVars then
    return .identity
  if (← synthInstance? (← mkAppM ``SpytialIdentity #[canon])).isSome then
    return .identity
  if (← synthInstance? (← mkAppM ``ToIdentityKey #[canon])).isSome then
    return .encoding
  discard <| synthInstance (← mkAppM ``ToIdentityKey #[canon])
  return .encoding

private meta def mkDerivCtx (declName : Name) : TermElabM DerivCtx := do
  let indVal ← getConstInfoInduct declName
  if indVal.numIndices > 0 then
    unsupported declName m!"inductive families (types with indices) are not supported"
  if indVal.isNested then
    unsupported declName m!"nested inductives are not supported"
  let typeInfos ← indVal.all.toArray.mapM getConstInfoInduct
  let memberNames := typeInfos.map (·.name)
  let argNames ← mkInductArgNames typeInfos[0]!
  let instName ← mkInstName ``SpytialIdentity declName
  let mut keyFnNames := #[]
  let mut eqvFnNames := #[]
  if typeInfos.size == 1 then
    keyFnNames := #[instName ++ `key]
    eqvFnNames := #[instName ++ `eqv]
  else
    for i in [:typeInfos.size] do
      keyFnNames := keyFnNames.push (instName ++ .mkSimple s!"key_{i+1}")
      eqvFnNames := eqvFnNames.push (instName ++ .mkSimple s!"eqv_{i+1}")
  let mut deps : Array Dep := #[]
  let mut members : Array MemberPlan := #[]
  for ti in typeInfos do
    let mut ctorPlans := #[]
    for ctorName in ti.ctors do
      let ci ← getConstInfoCtor ctorName
      let (kinds, deps') ← forallTelescopeReducing ci.type fun xs _ => do
        let params := xs.extract 0 ci.numParams
        let paramIds := params.mapIdx fun j p => (p.fvarId!, mkIdent argNames[j]!)
        let mut kinds : Array FieldKind := #[]
        let mut ds := deps
        for x in xs.extract ci.numParams xs.size do
          let xty ← whnfR (← inferType x)
          if ← isProofLikeType xty then
            kinds := kinds.push .proofLike
          else
            let recIdx? := match xty.getAppFn with
              | .const c _ => memberNames.findIdx? (· == c)
              | _ => none
            match recIdx? with
            | some j => kinds := kinds.push (.recursive j)
            | none =>
              let canon := xty.abstract params
              match ds.findIdx? (·.canon == canon) with
              | some di => kinds := kinds.push (.dep di)
              | none =>
                let type ← renderDepType declName paramIds xty
                let keyId := mkIdent (← mkFreshUserName `k)
                let eqvId := mkIdent (← mkFreshUserName `r)
                ds := ds.push { canon, type, keyId, eqvId }
                kinds := kinds.push (.dep (ds.size - 1))
        return (kinds, ds)
      deps := deps'
      ctorPlans := ctorPlans.push
        { ctorName, tag := shortName ctorName, numParams := ci.numParams, kinds }
    members := members.push { indVal := ti, ctorPlans }
  -- outside the ctor telescopes, so field-local instance binders cannot leak
  -- into the synthesis that decides each dependency's route
  deps ← deps.mapM fun d => return { d with path := ← depPath d.canon }
  return { argNames, members, deps, keyFnNames, eqvFnNames,
           usePartial := typeInfos.size > 1 }

private meta def mkKeyAlt (ctx : DerivCtx) (cp : CtorPlan) :
    TermElabM (TSyntax ``matchAlt) := do
  let keyArgs : Array Term := ctx.deps.map fun d => (d.keyId : Term)
  let mut ctorArgs : Array Term := #[]
  for _ in [:cp.numParams] do ctorArgs := ctorArgs.push (← `(_))
  let mut parts : Array Term := #[← `(IdentityKey.ofString $(quote cp.tag))]
  for kind in cp.kinds do
    match kind with
    | .proofLike => ctorArgs := ctorArgs.push (← `(_))
    | .recursive j =>
      let a := mkIdent (← mkFreshUserName `a)
      ctorArgs := ctorArgs.push a
      parts := parts.push (← `($(mkIdent ctx.keyFnNames[j]!) $keyArgs:term* $a))
    | .dep di =>
      let a := mkIdent (← mkFreshUserName `a)
      ctorArgs := ctorArgs.push a
      parts := parts.push (← `($(ctx.deps[di]!.keyId) $a))
  let pat ← `(@$(mkCIdent cp.ctorName):ident $ctorArgs:term*)
  `(matchAltExpr| | $pat:term => IdentityKey.ofList [$parts,*])

private meta def mkEqvAlt (ctx : DerivCtx) (cp : CtorPlan) :
    TermElabM (TSyntax ``matchAlt) := do
  let eqvArgs : Array Term := ctx.deps.map fun d => (d.eqvId : Term)
  let mut ctorArgs1 : Array Term := #[]
  let mut ctorArgs2 : Array Term := #[]
  for _ in [:cp.numParams] do
    ctorArgs1 := ctorArgs1.push (← `(_))
    ctorArgs2 := ctorArgs2.push (← `(_))
  let mut cmps : Array Term := #[]
  for kind in cp.kinds do
    match kind with
    | .proofLike =>
      ctorArgs1 := ctorArgs1.push (← `(_))
      ctorArgs2 := ctorArgs2.push (← `(_))
    | .recursive j =>
      let a := mkIdent (← mkFreshUserName `a)
      let b := mkIdent (← mkFreshUserName `b)
      ctorArgs1 := ctorArgs1.push a
      ctorArgs2 := ctorArgs2.push b
      cmps := cmps.push (← `($(mkIdent ctx.eqvFnNames[j]!) $eqvArgs:term* $a $b))
    | .dep di =>
      let a := mkIdent (← mkFreshUserName `a)
      let b := mkIdent (← mkFreshUserName `b)
      ctorArgs1 := ctorArgs1.push a
      ctorArgs2 := ctorArgs2.push b
      cmps := cmps.push (← `($(ctx.deps[di]!.eqvId) $a $b))
  let rhs ← if h : cmps.size = 0 then `(true) else
    cmps[1:].foldlM (init := cmps[0]) fun acc c => `($acc && $c)
  let pat1 ← `(@$(mkCIdent cp.ctorName):ident $ctorArgs1:term*)
  let pat2 ← `(@$(mkCIdent cp.ctorName):ident $ctorArgs2:term*)
  `(matchAltExpr| | $pat1:term, $pat2:term => $rhs)

open TSyntax.Compat in
private meta def mkAuxFn (ctx : DerivCtx) (m : MemberPlan) (i : Nat) (forKey : Bool) :
    TermElabM (TSyntax `command) := do
  let indApp ← mkInductiveApp m.indVal ctx.argNames
  let mut binders : Array (TSyntax ``bracketedBinder) := #[]
  for b in ← mkImplicitBinders ctx.argNames do
    binders := binders.push b
  for d in ctx.deps do
    let ty ← if forKey then `($(d.type) → IdentityKey) else `($(d.type) → $(d.type) → Bool)
    binders := binders.push (← `(explicitBinderF| ($(if forKey then d.keyId else d.eqvId) : $ty)))
  let targetNames := if forKey then #[`x] else #[`x, `y]
  let targets ← targetNames.mapM fun n => return mkIdent (← mkFreshUserName n)
  for t in targets do
    binders := binders.push (← `(explicitBinderF| ($t : $indApp)))
  let body ←
    if m.ctorPlans.isEmpty then
      `(nomatch $(targets[0]!))
    else do
      let discrs ← targets.mapM fun t => `(matchDiscr| $t:term)
      let mut alts : Array (TSyntax ``matchAlt) ← m.ctorPlans.mapM fun cp =>
        if forKey then mkKeyAlt ctx cp else mkEqvAlt ctx cp
      unless forKey do
        alts := alts.push (← `(matchAltExpr| | _, _ => false))
      `(match $[$discrs],* with $alts:matchAlt*)
  let retTy : Term ← if forKey then `(IdentityKey) else `(Bool)
  let fnName := mkIdent (if forKey then ctx.keyFnNames[i]! else ctx.eqvFnNames[i]!)
  if ctx.usePartial then
    `(partial def $fnName:ident $binders:bracketedBinder* : $retTy := $body)
  else
    `(def $fnName:ident $binders:bracketedBinder* : $retTy := $body)

open TSyntax.Compat in
private meta def mkInstanceCmd (ctx : DerivCtx) (declName : Name) :
    TermElabM (TSyntax `command) := do
  let some (m, i) := ctx.members.zipIdx.find? (fun (m, _) => m.indVal.name == declName)
    | unsupported declName m!"internal error: not a member of its own mutual block"
  let indVal := m.indVal
  let instName ← mkInstName ``SpytialIdentity declName
  let mut binders : Array (TSyntax ``bracketedBinder) := #[]
  for b in ← mkImplicitBinders ctx.argNames do
    binders := binders.push b
  for b in ← mkInstImplicitBinders ``SpytialIdentity indVal ctx.argNames do
    binders := binders.push b
  let indApp ← mkInductiveApp indVal ctx.argNames
  -- per-dep aux-function arguments: identity-routed deps pass the classifier
  -- bound by the presentation match below (`d.keyId`) or their induced
  -- decider; encoded deps pass `toKey`, a total classifier, in both arms
  let keyArgs : Array Term ← ctx.deps.mapM fun d => match d.path with
    | .identity => pure (d.keyId : Term)
    | .encoding => `((ToIdentityKey.toKey : $(d.type) → IdentityKey))
  let idDeps := ctx.deps.filter fun d => d.path matches .identity
  let viaTerm : Term ←
    if idDeps.isEmpty then
      if ctx.deps.isEmpty then
        `(IdentityVia.identity $(mkIdent ctx.keyFnNames[i]!))
      else
        `(IdentityVia.identity ($(mkIdent ctx.keyFnNames[i]!) $keyArgs:term*))
    else do
      let discrs ← idDeps.mapM fun d => do
        let t ← `(IdentityVia.classifier? (SpytialIdentity.viaOf $(d.type)))
        `(matchDiscr| $t:term)
      let somePats : Array Term ← idDeps.mapM fun d => `(Option.some $(d.keyId))
      let someRhs ← `(IdentityVia.identity ($(mkIdent ctx.keyFnNames[i]!) $keyArgs:term*))
      let underPats : Array Term ← idDeps.mapM fun _ => `(_)
      let eqvArgs : Array Term ← ctx.deps.mapM fun d => match d.path with
        | .identity => `(IdentityVia.toEqv (SpytialIdentity.viaOf $(d.type)))
        | .encoding =>
          `(fun a b => (ToIdentityKey.toKey : $(d.type) → IdentityKey) a
                    == (ToIdentityKey.toKey : $(d.type) → IdentityKey) b)
      let elseRhs ← `(IdentityVia.eqv ($(mkIdent ctx.eqvFnNames[i]!) $eqvArgs:term*))
      let alts := #[← `(matchAltExpr| | $[$somePats:term],* => $someRhs),
                    ← `(matchAltExpr| | $[$underPats:term],* => $elseRhs)]
      `(match $[$discrs],* with $alts:matchAlt*)
  `(instance $(mkIdent instName):ident $binders:bracketedBinder* : SpytialIdentity $indApp :=
      SpytialIdentity.mk $viaTerm Option.none)

/-- The key and eqv families each go in their own `mutual` block: members of a
    block share universe parameters, so mixing the families would give every
    function a phantom level parameter its use sites cannot determine. -/
private meta def mkFamilyBlock (ctx : DerivCtx) (forKey : Bool) :
    TermElabM (TSyntax `command) := do
  let mut defs : Array (TSyntax `command) := #[]
  for (m, i) in ctx.members.zipIdx do
    defs := defs.push (← mkAuxFn ctx m i forKey)
  `(mutual
      set_option match.ignoreUnusedAlts true
      $defs:command*
    end)

private meta def mkCmds (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkDerivCtx declName
  return #[← mkFamilyBlock ctx true, ← mkFamilyBlock ctx false,
           ← mkInstanceCmd ctx declName]

public meta def mkSpytialIdentityInstanceHandler (declNames : Array Name) :
    CommandElabM Bool := do
  let env ← getEnv
  unless declNames.all fun n => (env.find? n) matches some (.inductInfo _) do
    return false
  for declName in declNames do
    withoutExposeFromCtors declName do
      let cmds ← liftTermElabM <| mkCmds declName
      cmds.forM elabCommand
      modifyEnv (spytialStructuralExt.addEntry · declName)
  return true

meta initialize
  registerDerivingHandler ``SpytialIdentity mkSpytialIdentityInstanceHandler

end Identity

end SpytialLean
