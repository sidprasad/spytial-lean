module

public import SpytialLean.Types
public import Std.Data.String.ToNat

namespace SpytialLean

open Lean

/-!
# Typed decoding of Spytial data

The existing relationalizer remains the only producer of atoms and relations. It decides identity,
sharing, field names, and labels. This module supplies the inverse boundary for types that opt in:

```text
JsonDataInstance --reify (α := α)--> Except ReifyError α
```

`SpytialReify α` is deliberately independent of `SpytialIdentity α`. A graph decoder follows field
relations, so the same decoder handles both merged values and `asWritten` occurrences. A custom
identity that merges structurally different values may be lossy and therefore cannot in general
satisfy a round trip; such an identity is outside the reconstruction claim unless it retains enough
additional data.
-/

/-- A checked failure to reconstruct a typed value from relational data. -/
public structure ReifyError where
  message : String
  deriving Repr, DecidableEq, Inhabited

public instance : ToString ReifyError := ⟨ReifyError.message⟩

/-- An internal rooted view of a relational datum. The public `reify` API consumes the unmodified
`JsonDataInstance`; this view records its first atom while traversing field relations. -/
public structure ReifyDatum where
  root : String
  data : JsonDataInstance
  deriving Inhabited

public def reifyError (message : String) : Except ReifyError α :=
  .error ⟨message⟩

namespace ReifyDatum

/-- Use the first atom as the root, matching the ordering emitted by the existing relationalizer. -/
public def ofData (data : JsonDataInstance) : Except ReifyError ReifyDatum :=
  match data.atoms[0]? with
  | some atom => .ok { root := atom.id, data }
  | none => reifyError "reify: datum has no root atom"

/-- Look up exactly one atom by ID. Duplicate IDs make a datum ambiguous. -/
public def atom (datum : ReifyDatum) (id : String) : Except ReifyError JsonAtom :=
  match datum.data.atoms.toList.filter (·.id == id) with
  | [atom] => .ok atom
  | [] => reifyError s!"reify: unknown atom '{id}'"
  | _ => reifyError s!"reify: duplicate atom id '{id}'"

/-- Look up the unique child reached from `owner` through a binary field relation.

Repeated copies of the same tuple are treated extensionally. Distinct targets for one field are
ambiguous and rejected. Tuple-local types are checked against their referenced atoms; the decoder
does not reinterpret the existing relationalizer's relation-level naming or schema aggregation. -/
public def child (datum : ReifyDatum) (owner field : String) :
    Except ReifyError String := do
  let ownerAtom ← datum.atom owner
  let mut children : Array String := #[]
  for relation in datum.data.relations do
    if relation.name == field then
      for tuple in relation.tuples do
        if tuple.atoms[0]? == some owner then
          unless tuple.atoms.size == 2 do
            return ← reifyError s!"reify: relation '{field}' is not a binary field relation"
          unless tuple.types.size == 2 do
            return ← reifyError s!"reify: relation '{field}' has an invalid type signature"
          let child := tuple.atoms[1]!
          let childAtom ← datum.atom child
          unless tuple.types[0]! == ownerAtom.type && tuple.types[1]! == childAtom.type do
            return ← reifyError
              s!"reify: relation '{field}' has tuple types that disagree with its atoms"
          unless children.contains child do
            children := children.push child
  match children.toList with
  | [child] => .ok child
  | [] => reifyError s!"reify: atom '{owner}' has no '{field}' field"
  | _ => reifyError s!"reify: atom '{owner}' has multiple '{field}' fields"

/-- Look up an atom and check the type signature used by the existing relationalizer. -/
public def expectAtom (datum : ReifyDatum) (id expectedType : String) :
    Except ReifyError JsonAtom := do
  let atom ← datum.atom id
  if atom.type == expectedType then
    return atom
  reifyError s!"reify: atom '{id}' has type '{atom.type}', expected '{expectedType}'"

end ReifyDatum

/-- Opt-in support for reconstructing values of `α` from the existing Spytial relationalizer.

Instances decode one rooted atom with bounded recursion. The fuel is a malformed-input guard; the
public entry point supplies one more than the number of atoms in the datum. -/
public class SpytialReify (α : Type u) where
  reifyAt : ReifyDatum → String → Nat → Except ReifyError α

namespace SpytialReify

/-- Invoke the registered decoder at one atom. -/
public def decodeAt {α : Type u} [SpytialReify α]
    (datum : ReifyDatum) (root : String)
    (fuel : Nat) : Except ReifyError α :=
  SpytialReify.reifyAt datum root fuel

end SpytialReify

/-- Reconstruct a typed value from a rooted datum produced by Spytial's existing relationalizer. -/
public def reifyRooted {α : Type u} [SpytialReify α]
    (datum : ReifyDatum) : Except ReifyError α :=
  SpytialReify.decodeAt datum datum.root (datum.data.atoms.size + 1)

/-- Reconstruct a typed value from the exact `JsonDataInstance` consumed by Spytial.

For example, if `x : Tree` is a closed constructor value and `Tree` derives `SpytialReify`, the
integration property exercised by this package is:

```lean
let data ← SpytialLean.Reify.relationalizeValue x
unless reify (α := Tree) data = .ok x do
  throwError "round trip failed"
```

The expected type is explicit at the type level because Spytial's display-oriented type names are
not a complete encoding of Lean types. `reify` reads the first atom as the root, then reconstructs
constructor fields by following the existing relationalizer's relations; it does not recover a
stored copy of `x`.

The tested Tier 1 boundary is closed, constructor-reducible values made from `Nat` and `String`
literals and regular first-order, non-indexed inductive types (structures included) whose fields
also implement `SpytialReify`. Default structural identity and `SpytialIdentity.asWritten` both
preserve this property. Any custom identity used in the walked subtree must not merge structurally
unequal values.

The encoder is Lean metaprogramming, so the displayed integration property is not presently a
kernel theorem. `ReifyTest` checks it over the actual relationalizer and a generated family of
values. A theorem about this exact path would first require a pure, specified interface to the
existing relationalizer rather than a second encoder. Call `reifyRooted` only when an explicit root
is available. -/
public def reify {α : Type u} [SpytialReify α]
    (data : JsonDataInstance) : Except ReifyError α :=
  match ReifyDatum.ofData data with
  | .ok datum => reifyRooted datum
  | .error error => .error error

public def unquoteLabel? (label : String) : Option String :=
  if label.startsWith "\"" && label.endsWith "\"" then
    some ((label.drop 1).dropEnd 1).toString
  else
    none

public instance : SpytialReify Nat where
  reifyAt datum root fuel := do
    if fuel == 0 then return ← reifyError "reify Nat: decoder fuel exhausted"
    let atom ← datum.expectAtom root "Nat"
    match atom.label.toNat? with
    | some value => .ok value
    | none => reifyError "reify Nat: invalid decimal literal"

public instance : SpytialReify String where
  reifyAt datum root fuel := do
    if fuel == 0 then return ← reifyError "reify String: decoder fuel exhausted"
    let atom ← datum.expectAtom root "String"
    match unquoteLabel? atom.label with
    | some value => .ok value
    | none => reifyError "reify String: expected a quoted string label"

end SpytialLean
