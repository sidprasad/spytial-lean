module

public import SpytialLean.StructuralExposure

namespace SpytialLean

/-!
`deriving SpytialIdentity, SpytialReify, LosslessIdentity` certifies a supported concrete datatype.
`Structural.reify_relationalize_of_lossless` then proves that for every `x` of that type, the
unchecked shared walker followed by `reify` returns `Except.ok x`.

For a parameterized declaration, instantiate its parameters first, for example
`instance : LosslessIdentity (List Nat) := by spytial_lossless` proves the claim for every list.
The derivation enumerates reachable types, proves key injectivity by
induction, and proves compatibility between those types' reuse keys. It never enumerates values
or invokes the graph builder to decide whether a value round-trips.

Derivation requires the selected identity/exposure equations to be available. Public generated
equations are exported when this preserves instance selection; private/local dependencies retain
their existing visibility. Arbitrary custom or opaque classifiers may need manual evidence.
Abstract type parameters would additionally need compositional identity and cross-type
compatibility laws; this derivation deliberately operates on fully instantiated types instead.
The resulting equality is about the pure typed exposure and shared walker, not a universal claim
about expression elaboration in `MetaM`.

Exact reconstruction also preserves every pure textual inspector `alpha → String`, with any
printing options fixed. `Structural.inspect_reify_relationalize_of_lossless` states this law, with
`Structural.reifyRepr_relationalize_of_lossless` specializing it to Lean's `reprStr`. The scoped
import capability follows from value equality, rather than a separate assumption about printing.
-/

namespace StructuralExposure

@[simp] public theorem nodeOf_key {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (value : alpha) :
    StructuralEncoding.Node.key? (nodeOf value) =
      (ValueIdentity.key? value).map
        (fun key => (StructuralExposure.typeKey (alpha := alpha), key)) := by
  unfold nodeOf ExposedValue.withIdentity valueIdentity
  cases selected : ValueIdentity.key? value <;> rfl

public theorem identity_eq_of_node_key_eq {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (x y : alpha)
    (equal : StructuralEncoding.Node.key? (nodeOf x) = StructuralEncoding.Node.key? (nodeOf y)) :
    ValueIdentity.key? x = ValueIdentity.key? y := by
  have projected := congrArg (Option.map Prod.snd) equal
  simpa [nodeOf_key, Option.map_map, Function.comp_def] using projected

public theorem typeKey_eq_of_node_key {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (value : alpha) (key : IdentityKey × IdentityKey)
    (found : StructuralEncoding.Node.key? (nodeOf value) = some key) :
    StructuralExposure.typeKey (alpha := alpha) = key.1 := by
  rw [nodeOf_key] at found
  cases selected : ValueIdentity.key? value with
  | none => simp [selected] at found
  | some selectedKey =>
      simp only [selected, Option.map_some, Option.some.injEq] at found
      exact congrArg Prod.fst found

end StructuralExposure

/-- The selected identity policy preserves the entire exposed structure of every value.

This is an input identity law, not a hypothesis about a successful decoder or the output datum.
`deriving LosslessIdentity` proves it for a supported concrete type by induction and by checking all
reachable field-type pairs. It does not install or change an identity instance. -/
public class LosslessIdentity (alpha : Type u) [SpytialReify alpha]
    [StructuralReification alpha] [ValueIdentity alpha] [StructuralExposure alpha] : Prop where
  coherent : ∀ value : alpha, StructuralEncoding.Node.Coherent (StructuralExposure.nodeOf value)

/-- Every value of a type with a proved structural identity policy survives the unchecked,
identity-aware shared walker. No runtime representation check or fallback is involved. -/
public theorem Structural.reify_relationalize_of_lossless {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] [LosslessIdentity alpha] (value : alpha) :
    reify (relationalizeCandidate value) = Except.ok value :=
  reify_relationalizeCandidate_of_coherent value (LosslessIdentity.coherent value)

/-- Reconstructing an imported value preserves any pure textual inspection of that value.

For example, take `inspect := reprStr`, or fix the options of another value printer. The inspector
receives only the reconstructed value; it does not need the original value or source expression.
This is about value inspection, not the source text or declaration metadata displayed by `#print`.
The result holds for every value of every type satisfying the same laws as the round-trip theorem.
-/
public theorem Structural.inspect_reify_relationalize_of_lossless {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] [LosslessIdentity alpha] (inspect : alpha → String) (value : alpha) :
    (reify (relationalizeCandidate value)).map inspect = Except.ok (inspect value) := by
  rw [reify_relationalize_of_lossless]
  rfl

/-- Lean's `Repr` output is recoverable from the lossless typed import's rooted datum. -/
public theorem Structural.reifyRepr_relationalize_of_lossless {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] [LosslessIdentity alpha] [Repr alpha] (value : alpha) :
    reifyRepr (α := alpha) (relationalizeCandidate value) = Except.ok (reprStr value) :=
  reifyRepr_of_reify (reify_relationalize_of_lossless value)

end SpytialLean
