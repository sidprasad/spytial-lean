module

public import SpytialLean.Tier1Exposure

namespace SpytialLean

/-!
`deriving SpytialIdentity, SpytialReify, Tier1Lossless` gives a concrete Tier 1 datatype the theorem
`Tier1.reify_relationalize_of_lossless`: for every `x` of that type, the unchecked shared walker
followed by `reify` returns `Except.ok x`. The user does not supply an identity-coherence proof.

For a parameterized declaration, instantiate its parameters first, for example
`instance : Tier1Lossless (List Nat) := by spytial_lossless`. This proves the claim for *all* lists,
not just closed examples. The derivation enumerates reachable types, proves key injectivity by
induction, and proves compatibility between those types' reuse keys. It never enumerates values
or invokes the graph builder to decide whether a value round-trips.

Derivation requires the selected identity/exposure equations to be available. Public generated
equations are exported when this preserves instance selection; private/local dependencies retain
their existing visibility. Arbitrary custom or opaque classifiers may need manual evidence.
Abstract type parameters would additionally need compositional identity and cross-type
compatibility laws; this derivation deliberately operates on fully instantiated types instead.
The resulting equality is about the pure typed exposure and shared walker, not a universal claim
about expression elaboration in `MetaM`.
-/

namespace Tier1Exposure

@[simp] public theorem nodeOf_key {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] (value : alpha) :
    Tier1Structural.Node.key? (nodeOf value) =
      (ValueIdentity.key? value).map (fun key => (Tier1Exposure.typeKey (alpha := alpha), key)) := by
  unfold nodeOf ExposedValue.withIdentity valueIdentity
  cases selected : ValueIdentity.key? value <;> rfl

public theorem identity_eq_of_node_key_eq {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] (x y : alpha)
    (equal : Tier1Structural.Node.key? (nodeOf x) = Tier1Structural.Node.key? (nodeOf y)) :
    ValueIdentity.key? x = ValueIdentity.key? y := by
  have projected := congrArg (Option.map Prod.snd) equal
  simpa [nodeOf_key, Option.map_map, Function.comp_def] using projected

public theorem typeKey_eq_of_node_key {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] (value : alpha) (key : IdentityKey × IdentityKey)
    (found : Tier1Structural.Node.key? (nodeOf value) = some key) :
    Tier1Exposure.typeKey (alpha := alpha) = key.1 := by
  rw [nodeOf_key] at found
  cases selected : ValueIdentity.key? value with
  | none => simp [selected] at found
  | some selectedKey =>
      simp only [selected, Option.map_some, Option.some.injEq] at found
      exact congrArg Prod.fst found

end Tier1Exposure

/-- The selected identity policy preserves the entire exposed structure of every value.

This is an input identity law, not a hypothesis about a successful decoder or the output datum.
`deriving Tier1Lossless` proves it for a concrete Tier 1 type by induction and by checking all
reachable field-type pairs. It does not install or change an identity instance. -/
public class Tier1Lossless (alpha : Type u) [SpytialReify alpha]
    [Tier1Reification alpha] [ValueIdentity alpha] [Tier1Exposure alpha] : Prop where
  coherent : ∀ value : alpha, Tier1Structural.Node.Coherent (Tier1Exposure.nodeOf value)

/-- Every value of a type with a proved structural identity policy survives the unchecked,
identity-aware shared walker. No runtime representation check or fallback is involved. -/
public theorem Tier1.reify_relationalize_of_lossless {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] [Tier1Lossless alpha] (value : alpha) :
    reify (relationalizeCandidate value) = Except.ok value :=
  reify_relationalizeCandidate_of_coherent value (Tier1Lossless.coherent value)

end SpytialLean
