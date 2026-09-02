module

public import Lean
public meta import SpytialLean.TypeShape

namespace SpytialLean

open Lean Meta Elab

/-! # Declared identity for the Spytial relationalizer

`SpytialIdentity` declares, per type, which occurrences of a value merge into
one atom. No instance ⇒ the walker derives one on demand; `asWritten` declines
it. This module is the value layer; the walker (`Relationalizer`) consumes it. -/

private inductive KeyRep where
  | str (s : String)
  | nat (n : Nat)
  | node (ks : List KeyRep)
  | spelling (s : String)
  deriving BEq, Hashable, Repr, Inhabited

/-- Opaque identity token. Tupling from string/number leaves is injective:
    `ofList [ofString "leaf", ofNat 1]` can never encode the same token as
    `ofString "leaf1"`. -/
public structure IdentityKey where
  private rep : KeyRep
  deriving BEq, Hashable, Repr, Inhabited

public def IdentityKey.ofString (s : String) : IdentityKey := ⟨.str s⟩

public def IdentityKey.ofNat (n : Nat) : IdentityKey := ⟨.nat n⟩

public def IdentityKey.ofList (ks : List IdentityKey) : IdentityKey :=
  ⟨.node (ks.map (·.rep))⟩

/-- A distinct constructor underneath, so an opaque leaf's spelling key never
    collides with a structural or encoded key. -/
public def IdentityKey.ofSpelling (s : String) : IdentityKey := ⟨.spelling s⟩

/-- `toKey` must be injective, so parent identities built from it never conflate
    fields. Encoding a value grants no merge behavior on its own. -/
public class ToIdentityKey (α : Type u) where
  toKey : α → IdentityKey

-- Every encoding needs a meta twin in `MetaEncode.lean`; the cross-check in
-- `SpytialTests/IdentityWalkTest.lean` fails on a drifted twin or one without a
-- sample. A missing twin only costs the eval fallback.

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

/-! Each container lift tags its shape, so injectivity composes: `some []` and
`none` in `Option (List α)` can never encode alike. -/

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

/-- How a type presents its identity. The routes differ in cost: `identity` is
    one computation per subterm plus a lookup, `eqv` up to one comparison per
    existing group. `eqv`'s relation must be an equivalence — not `LawfulBEq`,
    which would outlaw the coarser-than-structural quotients this design exists
    for. `asWritten`'s induced decider is deliberately not reflexive. -/
public inductive IdentityVia (α : Type u) where
  | identity (f : α → IdentityKey)
  | eqv (r : α → α → Bool)
  | asWritten

/-- `@[expose]` with `viaOf`: a derived composite's `via` is a match on these,
    and a module context that cannot whnf it degrades the route to `.eqvRel`. -/
@[expose] public def IdentityVia.classifier? {α : Type u} : IdentityVia α → Option (α → IdentityKey)
  | .identity f => some f
  | .eqv _ => none
  | .asWritten => none

/-- The walker asks the compiled code, because a module-opaque instance body
    stops `whnf` short of the arm and the `.eqv` route it would otherwise fall
    back to memoizes per expression. -/
public def IdentityVia.isAsWritten {α : Type u} : IdentityVia α → Bool
  | .asWritten => true
  | _ => false

public def IdentityVia.toEqv {α : Type u} : IdentityVia α → (α → α → Bool)
  | .identity f => fun a b => f a == f b
  | .eqv r => r
  | .asWritten => fun _ _ => false

public def IdentityVia.comap {α : Type u} {β : Type v} (v : IdentityVia β) (n : α → β) :
    IdentityVia α :=
  match v with
  | .identity f => .identity (f ∘ n)
  | .eqv r => .eqv fun a b => r (n a) (n b)
  | .asWritten => .asWritten

/-- Subterms with the same identity merge into one atom. No instance ⇒ the
    walker supplies one; `SpytialIdentity.asWritten` opts back out. -/
public class SpytialIdentity (α : Type u) where
  via : IdentityVia α
  /-- The intended drawn representative of each identity class. Law:
      `identity (norm x) = identity x`. Not yet drawn — the walker's
      `norm?`-display TODO; merging is unaffected. -/
  norm? : Option (α → α) := none

/-- `@[expose]`: see `IdentityVia.classifier?`. -/
@[expose] public def SpytialIdentity.viaOf (α : Type u) [inst : SpytialIdentity α] : IdentityVia α :=
  inst.via

public def SpytialIdentity.runtimeKey? {α : Type u} [SpytialIdentity α] (a : α) :
    Option IdentityKey :=
  (SpytialIdentity.viaOf α).classifier? |>.map (· a)

/-- Writing this declares that `==` is an equivalence; a `BEq` instance
    existing never triggers merging. -/
@[reducible] public def SpytialIdentity.ofBEq {α : Type u} [BEq α] : SpytialIdentity α :=
  { via := .eqv (· == ·) }

/-- Opt out of the derive-on-demand default; also silences the decline warning. -/
@[reducible] public def SpytialIdentity.asWritten {α : Type u} : SpytialIdentity α :=
  { via := .asWritten }

/-- The `norm?` law holds exactly when `n` is idempotent. -/
@[reducible] public def SpytialIdentity.ofNorm {α : Type u} (n : α → α) (base : IdentityVia α) :
    SpytialIdentity α :=
  { via := base.comap n, norm? := some n }

/-! ## Views: Raw and Viewed -/

/-- `Raw.mk t` shifts the walk to `asWritten` for its whole subtree.
    Deliberately semireducible, so reducible-transparency instance search cannot
    see through it (pinned by test). The shift reads the value's spelling, not a
    declared field type: a field declared `Raw τ` but filled with a bare carrier
    value (defeq, so it typechecks) walks `declared`. -/
@[expose] public def Raw (α : Type u) : Type u := α

-- `@[expose]` on the `mk`s too: without it, module contexts cannot whnf-melt
-- the wrapper application, and the walker's unwrap relies on the melt.
@[expose] public def Raw.mk {α : Type u} (a : α) : Raw α := a

/-- The dual shift: back to `declared` for the subtree. -/
@[expose] public def Viewed (α : Type u) : Type u := α

@[expose] public def Viewed.mk {α : Type u} (a : α) : Viewed α := a

/-! ## Derived-structural registry -/

public meta initialize spytialStructuralExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, f) => s.insert n f
    addImportedFn := fun arrays =>
      arrays.foldl (fun s arr => arr.foldl (fun s (n, f) => s.insert n f) s) {}
  }

public meta def isSpytialStructural (env : Environment) (typeName : Name) : Bool :=
  spytialStructuralExt.getState env |>.contains typeName

public meta def structuralTwinName? (env : Environment) (typeName : Name) : Option Name :=
  spytialStructuralExt.getState env |>.find? typeName

/-! ## Deriving handler

Classifier-presented iff every identity-routed dependency has one; encoded
dependencies never force degradation. -/

public meta register_option spytial.identity.auto : Bool := {
  defValue := true
  descr := "supply a `SpytialIdentity` for types that declare none — the \
            primitives' `ToIdentityKey` encoding, else structural identity \
            derived on demand"
}

/-- `notApplicable` is silent; `refused` is a type that could plausibly have
    merged and did not, which is the only case worth a diagnostic. -/
public meta inductive DeriveResult where
  | derived
  | refused (why : MessageData)
  | notApplicable

/-- The class is `Type u`-indexed, so applying it to a proposition would be a
    type error rather than a decline. -/
public meta def isIdentityCandidate (ty : Expr) : MetaM Bool := do
  let .sort u ← whnf (← inferType ty) | return false
  return !u.isZero

private meta def installEncodedIdentity (ty : Expr) : MetaM Unit := do
  let tyStx ← PrettyPrinter.delab ty
  let cmd ← `(@[no_expose] instance : SpytialIdentity $tyStx :=
    SpytialIdentity.mk (IdentityVia.identity ToIdentityKey.toKey) Option.none)
  let env ← getEnv
  try
    Lean.liftCommandElabM <| Lean.Elab.Command.elabCommand cmd
    resetSynthInstanceCache
  catch _ => setEnv env

mutual

/-- The mutual recursion with `depPath` terminates: a field whose head is a
    member of the block being derived is `.recursive` and never reaches here,
    and Lean admits no cross-declaration type cycle outside a mutual block. -/
public meta partial def deriveIdentity (ty : Expr) : MetaM DeriveResult := do
  unless spytial.identity.auto.get (← getOptions) do return .notApplicable
  let ty ← whnf ty
  unless ← isIdentityCandidate ty do return .notApplicable
  let .const declName _ := ty.getAppFn | return .notApplicable
  unless (← getEnv).find? declName matches some (.inductInfo _) do
    return .notApplicable
  -- the derived instance binds one `[SpytialIdentity _]` per parameter
  for a in ty.getAppArgs do
    if ← isIdentityCandidate a then ensureIdentity a
  let env ← getEnv
  try
    Lean.liftCommandElabM <| Lean.Elab.applyDerivingHandlers ``SpytialIdentity #[declName]
    resetSynthInstanceCache
    return .derived
  catch e =>
    setEnv env
    return .refused e.toMessageData

/-- Encoding first: deriving first would key `Nat` by unary spine. -/
public meta partial def ensureIdentity (ty : Expr) : MetaM Unit := do
  if (← synthInstance? (← mkAppM ``SpytialIdentity #[ty])).isSome then return
  if (← synthInstance? (← mkAppM ``ToIdentityKey #[ty])).isSome then
    installEncodedIdentity ty
  else
    discard <| deriveIdentity ty

end

namespace Identity

open Lean.Elab.Deriving Lean.Parser.Term Command

private meta inductive DepPath where
  | identity
  | encoding
  deriving Inhabited

/-- A field type the generated code needs an identity for. Parameters are
    `Dep`s too — their `canon` is a loose bvar. -/
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
  metaFnNames : Array Name
  usePartial : Bool

private meta def unsupported (declName : Name) (msg : MessageData) : TermElabM α :=
  throwError "cannot derive `SpytialIdentity` for `{.ofConstName declName}`: {msg}"

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

/-- A dependency with loose bvars in `canon` is not synthesizable here and
    always routes through `SpytialIdentity` — the generated instance binds
    `[SpytialIdentity α]`, so containers merge iff their elements do. -/
private meta def depPath (canon : Expr) : TermElabM DepPath := do
  if canon.hasLooseBVars then
    return .identity
  if (← synthInstance? (← mkAppM ``SpytialIdentity #[canon])).isSome then
    return .identity
  if (← synthInstance? (← mkAppM ``ToIdentityKey #[canon])).isSome then
    return .encoding
  if (← deriveIdentity canon) matches .derived then
    if (← synthInstance? (← mkAppM ``SpytialIdentity #[canon])).isSome then
      return .identity
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
  let mut metaFnNames := #[]
  if typeInfos.size == 1 then
    keyFnNames := #[instName ++ `key]
    eqvFnNames := #[instName ++ `eqv]
    metaFnNames := #[instName ++ `metaKey]
  else
    for i in [:typeInfos.size] do
      keyFnNames := keyFnNames.push (instName ++ .mkSimple s!"key_{i+1}")
      eqvFnNames := eqvFnNames.push (instName ++ .mkSimple s!"eqv_{i+1}")
      metaFnNames := metaFnNames.push (instName ++ .mkSimple s!"metaKey_{i+1}")
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
  return { argNames, members, deps, keyFnNames, eqvFnNames, metaFnNames,
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
    `(@[no_expose] partial def $fnName:ident $binders:bracketedBinder* : $retTy := $body)
  else
    `(@[no_expose] def $fnName:ident $binders:bracketedBinder* : $retTy := $body)

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
  -- `@[no_expose]`: this body dispatches on each field type's own instance, so
  -- it must elaborate with private constants visible.
  `(@[no_expose] instance $(mkIdent instName):ident $binders:bracketedBinder* :
      SpytialIdentity $indApp := SpytialIdentity.mk $viaTerm Option.none)

/-- The key and eqv families each go in their own `mutual` block: members of a
    block share universe parameters, so mixing them would give every function a
    phantom level parameter its use sites cannot determine. -/
private meta def mkFamilyBlock (ctx : DerivCtx) (forKey : Bool) :
    TermElabM (TSyntax `command) := do
  let mut defs : Array (TSyntax `command) := #[]
  for (m, i) in ctx.members.zipIdx do
    defs := defs.push (← mkAuxFn ctx m i forKey)
  `(mutual
      set_option match.ignoreUnusedAlts true
      $defs:command*
    end)

/-- By dynamic name — `Identity` cannot import `MetaEncode` (it imports us). An
    absent twin bakes a `pure none` step, so a hand-written `ToIdentityKey`
    without a twin costs an evaluation, never a failed derive. -/
private meta def hasMetaEncode (canon : Expr) : TermElabM Bool := do
  let clsName := `SpytialLean.MetaEncode
  unless (← getEnv).contains clsName do return false
  try
    let u ← mkFreshLevelMVar
    return (← synthInstance? (mkApp (mkConst clsName [u]) canon)).isSome
  catch _ => return false

/-- Identity-routed and recursive fields go through the walker's `dispatch`, so
    subterm memoization stays central. A `none` step makes the arm `none`. -/
private meta def mkMetaCtorArm (ctx : DerivCtx) (cp : CtorPlan)
    (dispatchId argsId : Ident) : TermElabM Term := do
  let total := cp.numParams + cp.kinds.size
  let keyOfRef : Term := mkCIdent `SpytialLean.MetaEncode.keyOf?
  let mut pairs : Array (Term × Ident) := #[]
  for (kind, i) in cp.kinds.zipIdx do
    let idx := cp.numParams + i
    let step? : Option Term ← do
      match kind with
      | .proofLike => pure none
      | .recursive _ => some <$> `($dispatchId (($argsId)[$(quote idx)]!))
      | .dep di =>
        match ctx.deps[di]!.path with
        | .identity => some <$> `($dispatchId (($argsId)[$(quote idx)]!))
        | .encoding =>
          if ← hasMetaEncode ctx.deps[di]!.canon then
            some <$> `($keyOfRef $(ctx.deps[di]!.type) (($argsId)[$(quote idx)]!))
          else
            some <$> `((pure none : Lean.Meta.MetaM (Option IdentityKey)))
    if let some step := step? then
      pairs := pairs.push (step, mkIdent (← mkFreshUserName `k))
  let parts : Array Term :=
    #[← `(IdentityKey.ofString $(quote cp.tag))] ++ pairs.map (fun (_, k) => (k : Term))
  let mut body : Term ← `(pure (some (IdentityKey.ofList [$parts,*])))
  for (step, k) in pairs.reverse do
    body ← `(($step : Lean.Meta.MetaM (Option IdentityKey)) >>= fun
      | some $k => $body
      | none => pure none)
  -- `cond`, not `if`: spliced `if` syntax lacks the position info the do
  -- elaborator's control-flow inference wants; both arms are action values.
  `(cond (($argsId).size == $(quote total)) $body (pure none))

open TSyntax.Compat in
/-- Not recursive — every child goes through `dispatch` — so twins need no
    `mutual` block. -/
private meta def mkMetaFn (ctx : DerivCtx) (m : MemberPlan) (i : Nat) :
    TermElabM (TSyntax `command) := do
  let fnName := mkIdent ctx.metaFnNames[i]!
  let dispatchId := mkIdent (← mkFreshUserName `dispatch)
  let eId := mkIdent (← mkFreshUserName `e)
  let wId := mkIdent (← mkFreshUserName `w)
  let cId := mkIdent (← mkFreshUserName `c)
  let argsId := mkIdent (← mkFreshUserName `args)
  let opacityRef : Term := mkCIdent `SpytialLean.opacityKey?
  let mut body : Term ← `($opacityRef $wId)
  for cp in m.ctorPlans.reverse do
    let arm ← mkMetaCtorArm ctx cp dispatchId argsId
    body ← `(cond ($cId == $(quote cp.ctorName)) $arm $body)
  `(public meta def $fnName:ident
      ($dispatchId : Lean.Expr → Lean.Meta.MetaM (Option IdentityKey))
      ($eId : Lean.Expr) : Lean.Meta.MetaM (Option IdentityKey) :=
    Lean.Meta.whnf $eId >>= fun $wId =>
      match ($wId).getAppFn with
      | Lean.Expr.const $cId _ =>
        let $argsId := ($wId).getAppArgs
        $body
      | _ => pure none)

private meta def mkCmds (declName : Name) : TermElabM (Array Syntax × Option Name) := do
  let ctx ← mkDerivCtx declName
  let some i := ctx.members.findIdx? (·.indVal.name == declName)
    | unsupported declName m!"internal error: not a member of its own mutual block"
  let mut cmds := #[← mkFamilyBlock ctx true, ← mkFamilyBlock ctx false]
  -- No `MetaEncode` in scope: emit no twin — the generated code could not
  -- elaborate — and register nothing, so the walker takes the eval fallback.
  let mut twinName? := none
  if (← getEnv).contains `SpytialLean.opacityKey? then
    for (m, j) in ctx.members.zipIdx do
      cmds := cmds.push (← mkMetaFn ctx m j)
    twinName? := some ctx.metaFnNames[i]!
  cmds := cmds.push (← mkInstanceCmd ctx declName)
  return (cmds, twinName?)

public meta def mkSpytialIdentityInstanceHandler (declNames : Array Name) :
    CommandElabM Bool := do
  let env ← getEnv
  unless declNames.all fun n => (env.find? n) matches some (.inductInfo _) do
    return false
  for declName in declNames do
    withoutExposeFromCtors declName do
      let (cmds, twinName?) ← liftTermElabM <| mkCmds declName
      cmds.forM elabCommand
      if let some twinName := twinName? then
        -- register the name the twin actually got, or a namespaced type's meta
        -- lane silently dies
        let fullTwin := (← getCurrNamespace) ++ twinName
        modifyEnv (spytialStructuralExt.addEntry · (declName, fullTwin))
  return true

meta initialize
  registerDerivingHandler ``SpytialIdentity mkSpytialIdentityInstanceHandler

end Identity

end SpytialLean
