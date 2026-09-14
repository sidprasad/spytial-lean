module

public import SpytialLean.Types

namespace SpytialLean

open Lean

/-!
# Typed decoding of Spytial data

Spytial has one graph walker with two ways to expose input to it. The existing `MetaM` adapter
discovers structure from elaborated `Lean.Expr` values. For supported datatypes,
`deriving SpytialReify` generates ordinary pattern matching that exposes a typed value as the same
structural nodes. This module supplies the inverse boundary for those nodes:

```text
RootedJsonDataInstance --reify (α := α)--> Except ReifyError α
```

`SpytialReify α` is deliberately independent of `SpytialIdentity α`. A graph decoder follows field
relations, so the same decoder handles both merged values and `asWritten` occurrences. A custom
identity that merges structurally different values can make a raw graph lossy. Certified typed
exposure detects that case with the independent checker and asks the shared walker to preserve
occurrences; arbitrary graphs and the `MetaM` adapter carry no such guarantee.
-/

/-- A checked failure to reconstruct a typed value from relational data. -/
public structure ReifyError where
  message : String
  deriving Repr, DecidableEq, Inhabited

public instance : ToString ReifyError := ⟨ReifyError.message⟩

public def reifyError (message : String) : Except ReifyError α :=
  .error ⟨message⟩

namespace JsonDataInstance

/-- Look up exactly one atom by ID. Duplicate IDs make a datum ambiguous. -/
@[expose] public def atom (datum : JsonDataInstance) (id : String) : Except ReifyError JsonAtom :=
  match datum.atoms.toList.filter (·.id == id) with
  | [atom] => .ok atom
  | [] => reifyError s!"reify: unknown atom '{id}'"
  | _ => reifyError s!"reify: duplicate atom id '{id}'"

/-- The structural content of a field, independent of relation display names and metadata.
Records with the same structural ID contribute their tuples in order. -/
@[expose] public def fieldTuples (datum : JsonDataInstance) (ownerType field : String) :
    List JsonTuple :=
  (datum.relations.toList.filter
    (fun relation => relation.id == fieldRelationId ownerType field)).flatMap
      (fun relation => relation.tuples.toList)

/-- Look up the unique child reached from `owner` through a binary field relation.

The structural ID is determined by the owner's type and field name, so observations or unrelated
same-named relations cannot supply a field. Repeated copies of a tuple are treated extensionally;
distinct targets are rejected. Tuple-local types are checked against their referenced atoms. -/
@[expose] public def child (datum : JsonDataInstance) (owner field : String) :
    Except ReifyError String := do
  let ownerAtom ← datum.atom owner
  let mut children : Array String := #[]
  for tuple in (datum.fieldTuples ownerAtom.type field).filter
      (fun tuple => tuple.atoms[0]? == some owner) do
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

/-- Decode the child selected by a field relation using a caller-supplied decoder. -/
public def decodeChildWith (datum : JsonDataInstance) (owner field : String)
    (decode : String → Except ReifyError α) : Except ReifyError α :=
  match datum.child owner field with
  | .error error => .error error
  | .ok child => decode child

/-- Check a field relation using a caller-supplied structural checker. -/
@[expose] public def childRepresentsWith (datum : JsonDataInstance) (owner field : String)
    (represents : String → α → Bool) (value : α) : Bool :=
  match datum.child owner field with
  | .error _ => false
  | .ok child => represents child value

/-- Lift a pointwise implication between structural checkers through a field lookup. -/
public theorem childRepresentsWith_mono
    {datum : JsonDataInstance} {owner field : String}
    {source : String → α → Bool} {target : String → β → Bool}
    {sourceValue : α} {targetValue : β}
    (complete : ∀ child, source child sourceValue = true → target child targetValue = true)
    (represented : datum.childRepresentsWith owner field source sourceValue = true) :
    datum.childRepresentsWith owner field target targetValue = true := by
  unfold childRepresentsWith at represented ⊢
  cases hc : datum.child owner field with
  | error error => simp [hc] at represented
  | ok child =>
      simp only [hc] at represented ⊢
      exact complete child represented

/-- Conjunction preserves pointwise implications between Boolean checks. -/
public theorem boolAnd_eq_true_mono {leftSource rightSource leftTarget rightTarget : Bool}
    (leftComplete : leftSource = true → leftTarget = true)
    (rightComplete : rightSource = true → rightTarget = true)
    (represented : (leftSource && rightSource) = true) :
    (leftTarget && rightTarget) = true := by
  cases leftSource <;> cases rightSource <;> simp_all

/-- A structurally represented child is successfully decoded. -/
public theorem decodeChildWith_complete
    {datum : JsonDataInstance} {owner field : String}
    {decode : String → Except ReifyError α} {represents : String → α → Bool} {value : α}
    (complete : ∀ child, represents child value = true → decode child = Except.ok value)
    (h : childRepresentsWith datum owner field represents value = true) :
    decodeChildWith datum owner field decode = Except.ok value := by
  unfold childRepresentsWith at h
  unfold decodeChildWith
  cases hc : datum.child owner field with
  | error error => simp [hc] at h
  | ok child =>
      simp only [hc] at h ⊢
      exact complete child h

/-- Look up an atom and check the type signature used by the existing relationalizer. -/
@[expose] public def expectAtom (datum : JsonDataInstance) (id expectedType : String) :
    Except ReifyError JsonAtom := do
  let atom ← datum.atom id
  if atom.type == expectedType then
    return atom
  reifyError s!"reify: atom '{id}' has type '{atom.type}', expected '{expectedType}'"

/-- Check the root atom and constructor label before checking its fields. -/
@[expose] public def constructorRepresents (datum : JsonDataInstance)
    (root expectedType label : String) (fieldsRepresent : Bool) : Bool :=
  match datum.expectAtom root expectedType with
  | .error _ => false
  | .ok atom => atom.label == label && fieldsRepresent

/-- Changing field checks by implication preserves constructor representation. -/
public theorem constructorRepresents_mono
    {datum : JsonDataInstance} {root expectedType label : String}
    {source target : Bool} (complete : source = true → target = true)
    (represented : datum.constructorRepresents root expectedType label source = true) :
    datum.constructorRepresents root expectedType label target = true := by
  unfold constructorRepresents at represented ⊢
  cases atom : datum.expectAtom root expectedType with
  | error error => simp [atom] at represented
  | ok value =>
      simp only [atom, Bool.and_eq_true] at represented ⊢
      exact ⟨represented.1, complete represented.2⟩

end JsonDataInstance

/-- Opt-in support for reconstructing values of `α` from the existing Spytial relationalizer.

Instances decode one rooted atom with bounded recursion. The fuel is a malformed-input guard; the
public entry point supplies one more than the number of atoms in the datum. -/
public class SpytialReify (α : Type u) where
  reifyAt : JsonDataInstance → String → Nat → Except ReifyError α

/-- A kernel-checkable structural interpretation of the graph accepted by a reifier.

`representsAt datum root fuel value` inspects atoms and field relations; it must not be defined by
calling `reifyAt`. The law says that this independent graph check is sufficient for decoding.
Primitive instances and instances generated by `deriving SpytialReify` provide the checker and its
proof together. -/
public class StructuralReification (α : Type u) [SpytialReify α] where
  representsAt : JsonDataInstance → String → Nat → α → Bool
  reifyAt_complete : ∀ datum root fuel value,
    representsAt datum root fuel value = true →
      SpytialReify.reifyAt datum root fuel = Except.ok value

namespace SpytialReify

/-- Invoke the registered decoder at one atom. -/
public def decodeAt {α : Type u} [SpytialReify α]
    (datum : JsonDataInstance) (root : String)
    (fuel : Nat) : Except ReifyError α :=
  SpytialReify.reifyAt datum root fuel

end SpytialReify

namespace StructuralReification

/-- The registered structural graph checker is sufficient for the registered decoder. -/
public theorem decodeAt_complete { α : Type u } [SpytialReify α] [StructuralReification α]
    {datum : JsonDataInstance} {root : String} {fuel : Nat} {value : α}
    (h : StructuralReification.representsAt datum root fuel value = true) :
    SpytialReify.decodeAt datum root fuel = Except.ok value :=
  StructuralReification.reifyAt_complete datum root fuel value h

end StructuralReification

/-- Reconstruct a typed value from a Spytial datum with an explicit root atom.

The expected type is explicit at the type level because Spytial's display-oriented type names are
not a complete encoding of Lean types. The root is an atom ID carried alongside the underlying
relational instance; atom-array order has no semantic role. `reify` reconstructs constructor fields
by following the existing relationalizer's relations and does not recover a stored copy of `x`.

Automatic deriving supports regular first-order, non-indexed inductive types (structures included)
over supported primitives. Explicit, implicit, strict-implicit, and instance-implicit data fields
are reconstructed; their computed field-relation names must be pairwise distinct within each
constructor. Datatype parameters require `SpytialReify` and `StructuralReification` instances.
The supplied foundations are `Nat` and `String`, with derived instances for `Bool`, `PUnit`, `Int`,
`Option`, `Prod`, `Sum`, and `List`. Dependent/indexed families, mutual, nested, or non-regular
recursion, and proof-, type-, or function-valued fields are outside this derivation fragment.

The scoped capability is lossless import under a lossless identity policy: if a datum reconstructs
`x`, applying any pure value inspector to that result reproduces its output on `x`. For example,
`reifyRepr` reconstructs the value before applying Lean's `reprStr`; no saved printout is needed.

`reify_of_structurallyRepresents` proves reconstruction for any structurally representing datum.
`Structural.reify_relationalize_of_lossless` proves the round trip for types with `LosslessIdentity`,
through the shared engine for every value and with the selected identity policy.
`relationalize%` exposes that pure computation for compatible closed expressions. Separately,
opt-in `spytial.certifyReification` kernel-checks reconstruction of the exact datum emitted by
`#spytial` or `relationalize%`. The integration needs the generated instances and executable host
code (a `meta import` for imported definitions). These are setup requirements for the capability,
not a claim that every expression or inspection mode is handled by the proved route. -/
public def reify {α : Type u} [SpytialReify α]
    (datum : RootedJsonDataInstance) : Except ReifyError α :=
  SpytialReify.decodeAt datum.data datum.root (datum.data.atoms.size + 1)

/-- Decide whether a datum structurally represents `value` according to its registered checker. -/
@[expose] public def structurallyRepresents { α : Type u }
    [SpytialReify α] [StructuralReification α]
    (datum : RootedJsonDataInstance) (value : α) : Bool :=
  StructuralReification.representsAt datum.data datum.root (datum.data.atoms.size + 1) value

/-- A kernel-visible claim that the relational datum has the structure of `value`. -/
public abbrev StructurallyRepresents { α : Type u } [SpytialReify α] [StructuralReification α]
    (datum : RootedJsonDataInstance) (value : α) : Prop :=
  structurallyRepresents datum value = true

/-- Universal structural reconstruction theorem.

This theorem is independent of `MetaM`: once a concrete datum is shown to structurally represent
`value`, the pure reifier reconstructs `value` under Lean equality. -/
public theorem reify_of_structurallyRepresents
    { α : Type u } [SpytialReify α] [StructuralReification α]
    {datum : RootedJsonDataInstance} {value : α} (h : StructurallyRepresents datum value) :
    reify datum = Except.ok value := by
  unfold StructurallyRepresents structurallyRepresents at h
  unfold reify
  exact StructuralReification.decodeAt_complete h

/-- Reconstruct the standard `Repr` string from a typed relational datum. -/
public def reifyRepr { α : Type u } [SpytialReify α] [Repr α]
    (datum : RootedJsonDataInstance) : Except ReifyError String :=
  (reify (α := α) datum).map reprStr

/-- Any proof of value reconstruction also proves preservation of its `Repr` output. -/
public theorem reifyRepr_of_reify
    {α : Type u} [SpytialReify α] [Repr α]
    {datum : RootedJsonDataInstance} {value : α} (h : reify datum = Except.ok value) :
    reifyRepr (α := α) datum = Except.ok (reprStr value) := by
  rw [reifyRepr, h]
  rfl

/-- Structural reconstruction is sufficient to reproduce the host value's `Repr` output. -/
public theorem reifyRepr_of_structurallyRepresents
    { α : Type u } [SpytialReify α] [StructuralReification α] [Repr α]
    {datum : RootedJsonDataInstance} {value : α} (h : StructurallyRepresents datum value) :
    reifyRepr (α := α) datum = Except.ok (reprStr value) := by
  rw [reifyRepr, reify_of_structurallyRepresents h]
  rfl

@[expose] public def decimalDigit? (character : Char) : Option Nat :=
  if character.isDigit then some (character.toNat - '0'.toNat) else none

@[expose] public def parseNatDigits (accumulator : Nat) : List Char → Option Nat
  | [] => some accumulator
  | character :: characters =>
      match decimalDigit? character with
      | none => none
      | some digit => parseNatDigits (10 * accumulator + digit) characters

/-- Parse the decimal spelling emitted for a `Nat` atom by the existing relationalizer. -/
@[expose] public def parseNatLabel? (label : String) : Option Nat :=
  match label.toList with
  | [] => none
  | character :: characters =>
      match decimalDigit? character with
      | none => none
      | some digit => parseNatDigits digit characters

private theorem parseNatDigits_eq_ofDigitChars (accumulator : Nat) (characters : List Char)
    (digits : ∀ character ∈ characters, character.isDigit) :
    parseNatDigits accumulator characters =
      some (Nat.ofDigitChars 10 characters accumulator) := by
  induction characters generalizing accumulator with
  | nil => simp [parseNatDigits]
  | cons character characters inductionHypothesis =>
      have headDigit : character.isDigit := digits character (by simp)
      have tailDigits : ∀ tail ∈ characters, tail.isDigit := by
        intro tail member
        exact digits tail (by simp [member])
      simp [parseNatDigits, decimalDigit?, headDigit, Nat.ofDigitChars_cons,
        inductionHypothesis _ tailDigits]

/-- The transparent parser accepts every `Nat` label emitted by relationalization. -/
@[simp] public theorem parseNatLabel?_repr (value : Nat) :
    parseNatLabel? value.repr = some value := by
  unfold parseNatLabel?
  rw [Nat.toList_repr]
  cases digitsEquation : Nat.toDigits 10 value with
  | nil => exact False.elim (Nat.toDigits_ne_nil digitsEquation)
  | cons character characters =>
      have headMember : character ∈ Nat.toDigits 10 value := by
        rw [digitsEquation]
        simp
      have headDigit : character.isDigit :=
        Nat.isDigit_of_mem_toDigits (b := 10) (n := value) (by decide) (by decide) headMember
      have tailDigits : ∀ tail ∈ characters, tail.isDigit := by
        intro tail member
        have tailMember : tail ∈ Nat.toDigits 10 value := by
          rw [digitsEquation]
          simp [member]
        exact Nat.isDigit_of_mem_toDigits (b := 10) (n := value)
          (by decide) (by decide) tailMember
      simp only [decimalDigit?, headDigit, ↓reduceIte]
      rw [parseNatDigits_eq_ofDigitChars _ _ tailDigits]
      apply congrArg some
      have emitted := Nat.ofDigitChars_ten_toDigits (n := value)
      rw [digitsEquation, Nat.ofDigitChars_cons] at emitted
      simpa using emitted

@[expose] public def unquoteLabel? (label : String) : Option String :=
  match label.toList with
  | '\"' :: characters =>
      match characters.reverse with
      | '\"' :: body => some (String.ofList body.reverse)
      | _ => none
  | _ => none

public def reifyNatAt (datum : JsonDataInstance) (root : String) (fuel : Nat) :
    Except ReifyError Nat :=
  match fuel with
  | 0 => reifyError "reify Nat: decoder fuel exhausted"
  | _ + 1 =>
      match datum.expectAtom root "Nat" with
      | .error error => .error error
      | .ok atom =>
          match parseNatLabel? atom.label with
          | some value => .ok value
          | none => reifyError "reify Nat: invalid decimal literal"

public instance : SpytialReify Nat := ⟨reifyNatAt⟩

@[expose] public def natRepresentsAt
    (datum : JsonDataInstance) (root : String) (fuel : Nat) (value : Nat) : Bool :=
  match fuel with
  | 0 => false
  | _ + 1 =>
      match datum.expectAtom root "Nat" with
      | .error _ => false
      | .ok atom => parseNatLabel? atom.label == some value

public theorem reifyNatAt_complete {datum : JsonDataInstance} {root : String} {fuel value : Nat}
    (h : natRepresentsAt datum root fuel value = true) :
    reifyNatAt datum root fuel = Except.ok value := by
  cases fuel with
  | zero => simp [natRepresentsAt] at h
  | succ fuel =>
      cases ha : datum.expectAtom root "Nat" with
      | error error => simp [natRepresentsAt, ha] at h
      | ok atom =>
          simp only [natRepresentsAt, ha, beq_iff_eq] at h
          simp [reifyNatAt, ha, h]

public instance : StructuralReification Nat where
  representsAt := natRepresentsAt
  reifyAt_complete := by
    intro datum root fuel value h
    exact reifyNatAt_complete h

public def reifyStringAt (datum : JsonDataInstance) (root : String) (fuel : Nat) :
    Except ReifyError String :=
  match fuel with
  | 0 => reifyError "reify String: decoder fuel exhausted"
  | _ + 1 =>
      match datum.expectAtom root "String" with
      | .error error => .error error
      | .ok atom =>
          match unquoteLabel? atom.label with
          | some value => .ok value
          | none => reifyError "reify String: expected a quoted string label"

public instance : SpytialReify String := ⟨reifyStringAt⟩

@[expose] public def stringRepresentsAt
    (datum : JsonDataInstance) (root : String) (fuel : Nat) (value : String) : Bool :=
  match fuel with
  | 0 => false
  | _ + 1 =>
      match datum.expectAtom root "String" with
      | .error _ => false
      | .ok atom => atom.label == "\"" ++ value ++ "\""

public theorem reifyStringAt_complete
    {datum : JsonDataInstance} {root : String} {fuel : Nat} {value : String}
    (h : stringRepresentsAt datum root fuel value = true) :
    reifyStringAt datum root fuel = Except.ok value := by
  cases fuel with
  | zero => simp [stringRepresentsAt] at h
  | succ fuel =>
      cases ha : datum.expectAtom root "String" with
      | error error => simp [stringRepresentsAt, ha] at h
      | ok atom =>
          simp only [stringRepresentsAt, ha, beq_iff_eq] at h
          simp [reifyStringAt, ha, h, unquoteLabel?]

public instance : StructuralReification String where
  representsAt := stringRepresentsAt
  reifyAt_complete := by
    intro datum root fuel value h
    exact reifyStringAt_complete h

end SpytialLean
