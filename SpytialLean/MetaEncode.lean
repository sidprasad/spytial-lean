module

public import Lean
public meta import SpytialLean.Identity
public meta import SpytialLean.TypeShape

namespace SpytialLean

open Lean Meta

/-! # MetaEncode — meta twins of the `ToIdentityKey` encodings

The walker holds `Expr`s, and `toKey` cannot see one, so each encoding has a
meta twin computing the same key from a closed value's `Expr` without
evaluation. The twins mirror `Identity.lean`'s instances one-to-one, in
order; agreement is pinned byte-for-byte by the enumerating cross-check in
`tests/IdentityWalkTest.lean`, and the walker falls back to evaluating the
compiled classifier where a twin is missing or stuck — slower, never wrong. -/

/-- `some n` for a value of type `Nat`, without evaluating through opacity
    barriers (default-transparency `whnf` only). -/
public meta partial def natValue? (v : Expr) : MetaM (Option Nat) := do
  if let some n ← getNatValue? v then return some n
  let w ← whnf v
  if let some n := getRawNatValue? w then return some n
  if let some n ← getNatValue? w then return some n
  if w.isAppOfArity ``Nat.succ 1 then
    if let some n ← natValue? w.appArg! then return some (n + 1)
  return none

/-- Drill a numeric wrapper's whnf normal form — nested single-data-field
    constructors (`Char.mk`/`UInt8.ofBitVec`/`BitVec.ofFin`/`Fin.mk`, …) —
    down to the underlying `Nat` literal: exactly the `.toNat` the
    corresponding encodings write. -/
public meta partial def drillNatValue? (v : Expr) (fuel : Nat := 8) : MetaM (Option Nat) := do
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let w ← whnf v
    if let some n := getRawNatValue? w then return some n
    let .const c _ := w.getAppFn | return none
    let some (.ctorInfo ci) := (← getEnv).find? c | return none
    let args := w.getAppArgs
    let mut dataField? : Option Expr := none
    for f in args.extract ci.numParams args.size do
      unless ← isProofLikeType (← inferType f) do
        if dataField?.isSome then return none
        dataField? := some f
    let some f := dataField? | return none
    drillNatValue? f fuel

/-- Collect the element expressions of a literal `List` value. -/
public meta partial def listElems? (v : Expr) (acc : Array Expr := #[]) :
    MetaM (Option (Array Expr)) := do
  let w ← whnf v
  if w.isAppOfArity ``List.nil 1 then return some acc
  if w.isAppOfArity ``List.cons 3 then
    let args := w.getAppArgs
    return ← listElems? args[2]! (acc.push args[1]!)
  return none

/-- Key a value whose head is `@[irreducible]` or `opaque` by its printed
    form, without unfolding it. Safe because `ofSpelling` is a separate
    constructor (a spelling key cannot collide with a real key) and the
    printer is `dbgToString` (distinct terms never print alike). Only the
    default machinery stops at these barriers — an explicit `.identity` or
    `.eqv` instance still runs the user's own function. -/
public meta def opacityKey? (v : Expr) : MetaM (Option IdentityKey) := do
  let w ← whnf v
  let .const c _ := w.getAppFn | return none
  if ← isIrreducible c then return some (.ofSpelling (toString w))
  if (← getConstInfo c) matches .opaqueInfo _ then return some (.ofSpelling (toString w))
  return none

/-- Meta twin of `ToIdentityKey α`: the key `toKey` computes from the value,
    computed from a closed value's `Expr` instead, without evaluation; `none`
    when the value is stuck. Resolve through `MetaEncode.keyOf?`, which adds
    the opacity gate. -/
public meta class MetaEncode (α : Type u) where
  metaKey : Expr → MetaM (Option IdentityKey)

/-- `metaKey` under the opacity gate: a stuck value with a deliberately opaque
    head keys by its spelling. The form the container twins use for their
    elements and generated code uses at encoded fields. -/
public meta def MetaEncode.keyOf? (α : Type u) [MetaEncode α] (v : Expr) :
    MetaM (Option IdentityKey) := do
  match ← MetaEncode.metaKey (α := α) v with
  | some k => return some k
  | none => opacityKey? v

/-- Pin a hand-written twin byte-for-byte against its encoding, e.g.
    `#eval MetaEncode.check "mytype" (v : MyType)`. Fails when the twin
    cannot key the literal or disagrees with `toKey`. -/
public meta def MetaEncode.check {α : Type} [ToIdentityKey α] [MetaEncode α] [ToExpr α]
    (label : String) (v : α) : MetaM Unit := do
  let some mkKey ← MetaEncode.keyOf? α (toExpr v)
    | throwError "{label}: twin failed on a literal"
  let rk := ToIdentityKey.toKey v
  unless mkKey == rk do
    throwError "{label}: twin {repr mkKey} ≠ toKey {repr rk}"

public meta instance : MetaEncode Nat where
  metaKey v := return (← natValue? v).map ToIdentityKey.toKey

public meta instance : MetaEncode String where
  metaKey v := do
    if let some s := getStringValue? v then return some (.ofString s)
    return (getStringValue? (← whnf v)).map .ofString

public meta instance : MetaEncode Bool where
  metaKey v := do
    let w ← whnf v
    if w.isConstOf ``Bool.true then return some (ToIdentityKey.toKey true)
    if w.isConstOf ``Bool.false then return some (ToIdentityKey.toKey false)
    return none

public meta instance : MetaEncode Char where
  metaKey v := do
    if let some c ← getCharValue? v then return some (.ofNat c.toNat)
    return (← drillNatValue? v).map .ofNat

public meta instance : MetaEncode Int where
  metaKey v := do
    if let some i ← getIntValue? v then return some (ToIdentityKey.toKey i)
    let w ← whnf v
    if w.isAppOfArity ``Int.ofNat 1 then
      return (← natValue? w.appArg!).map (ToIdentityKey.toKey <| Int.ofNat ·)
    if w.isAppOfArity ``Int.negSucc 1 then
      return (← natValue? w.appArg!).map (ToIdentityKey.toKey <| Int.negSucc ·)
    if let some i ← getIntValue? w then return some (ToIdentityKey.toKey i)
    return none

public meta instance : MetaEncode UInt8 where
  metaKey v := return (← drillNatValue? v).map .ofNat

public meta instance : MetaEncode UInt16 where
  metaKey v := return (← drillNatValue? v).map .ofNat

public meta instance : MetaEncode UInt32 where
  metaKey v := return (← drillNatValue? v).map .ofNat

public meta instance : MetaEncode UInt64 where
  metaKey v := return (← drillNatValue? v).map .ofNat

-- No `USize` twin: its width is platform-opaque (`System.Platform.numBits`),
-- so a literal's `% 2^width` never reduces meta-side — eval fallback owns it.

public meta instance {α : Type u} [MetaEncode α] : MetaEncode (List α) where
  metaKey v := do
    let some elems ← listElems? v | return none
    let mut parts := #[IdentityKey.ofString "list"]
    for el in elems do
      let some k ← MetaEncode.keyOf? α el | return none
      parts := parts.push k
    return some (.ofList parts.toList)

public meta instance {α : Type u} [MetaEncode α] : MetaEncode (Array α) where
  metaKey v := do
    let w ← whnf v
    unless w.isAppOfArity ``Array.mk 2 do return none
    let some elems ← listElems? w.appArg! | return none
    let mut parts := #[IdentityKey.ofString "array"]
    for el in elems do
      let some k ← MetaEncode.keyOf? α el | return none
      parts := parts.push k
    return some (.ofList parts.toList)

public meta instance {α : Type u} [MetaEncode α] : MetaEncode (Option α) where
  metaKey v := do
    let w ← whnf v
    if w.isAppOfArity ``Option.none 1 then
      return some (.ofList [.ofString "none"])
    if w.isAppOfArity ``Option.some 2 then
      let some k ← MetaEncode.keyOf? α w.appArg! | return none
      return some (.ofList [.ofString "some", k])
    return none

public meta instance {α : Type u} {β : Type v} [MetaEncode α] [MetaEncode β] :
    MetaEncode (α × β) where
  metaKey v := do
    let w ← whnf v
    unless w.isAppOfArity ``Prod.mk 4 do return none
    let args := w.getAppArgs
    let some k1 ← MetaEncode.keyOf? α args[2]! | return none
    let some k2 ← MetaEncode.keyOf? β args[3]! | return none
    return some (.ofList [.ofString "prod", k1, k2])

end SpytialLean
