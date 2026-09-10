module

public import SpytialLean.ReifyInstances
public import SpytialLean.Tier1Lossless
public meta import SpytialLean.Tier1LosslessDeriving
public meta import SpytialLean.ReifyInstances
public meta import Lean.Util.CollectAxioms

open SpytialLean

namespace Tier1LosslessTest

public structure Pair where
  left : Nat
  right : Nat
  deriving SpytialIdentity, SpytialReify, Tier1Lossless

public theorem pair_roundTrip (value : Pair) :
    reify (Tier1.relationalizeCandidate value) = Except.ok value :=
  Tier1.reify_relationalize_of_lossless value

public inductive Tree where
  | leaf (value : Nat)
  | branch (left right : Tree)
  deriving SpytialIdentity, SpytialReify, Tier1Lossless

public theorem tree_roundTrip (value : Tree) :
    reify (Tier1.relationalizeCandidate value) = Except.ok value :=
  Tier1.reify_relationalize_of_lossless value

public instance : Tier1Lossless (List Nat) := by spytial_lossless
public instance : Tier1Lossless (Option String) := by spytial_lossless
public instance : Tier1Lossless Int := by spytial_lossless
public instance : Tier1Lossless (Sum Nat String) := by spytial_lossless
public instance : Tier1Lossless PUnit := by spytial_lossless

public theorem list_roundTrip (value : List Nat) :
    reify (Tier1.relationalizeCandidate value) = Except.ok value :=
  Tier1.reify_relationalize_of_lossless value

public structure Forest where
  left : Tree
  right : Tree
  deriving SpytialIdentity, SpytialReify, Tier1Lossless

public structure Lists where
  first : List Nat
  rest : List (List Nat)
  deriving SpytialReify, Tier1Lossless

public theorem lists_roundTrip (value : Lists) :
    reify (Tier1.relationalizeCandidate value) = Except.ok value :=
  Tier1.reify_relationalize_of_lossless value

public inductive Empty where
  deriving SpytialIdentity, SpytialReify, Tier1Lossless

section Instantiated

public instance : SpytialIdentity Nat where
  via := .identity ToIdentityKey.toKey

public instance : SpytialIdentity Bool where
  via := .identity ToIdentityKey.toKey

public inductive Branch (alpha : Type) where
  | leaf (value : alpha)
  | branch (left right : Branch alpha)
  deriving SpytialIdentity, SpytialReify

public structure Mixed where
  left : Branch Nat
  right : Branch Bool
  deriving SpytialReify, Tier1Lossless

public theorem mixed_roundTrip (value : Mixed) :
    reify (Tier1.relationalizeCandidate value) = Except.ok value :=
  Tier1.reify_relationalize_of_lossless value

end Instantiated

public inductive Unshared where
  | leaf (value : String)
  | next (child : Unshared)
  deriving SpytialReify

public instance : SpytialIdentity Unshared := SpytialIdentity.asWritten
deriving instance Tier1Lossless for Unshared

public theorem unshared_roundTrip (value : Unshared) :
    reify (Tier1.relationalizeCandidate value) = Except.ok value :=
  Tier1.reify_relationalize_of_lossless value

public inductive Lossy where
  | leaf (value : Nat)
  | next (child : Lossy)
  deriving SpytialReify

public instance : SpytialIdentity Lossy where
  via := .identity (fun _ => IdentityKey.ofNat 0)

example : True := by
  fail_if_success have : Tier1Lossless Lossy := by spytial_lossless
  trivial

namespace TypeCollision

-- Both selected value classifiers are injective, but the two types deliberately share a tag.
-- Certifying each type in isolation would miss the resulting cross-type merge.
local instance : Tier1Exposure Bool :=
  let base : Tier1Exposure Bool := inferInstance
  { base with
    typeKey := natTypeKey
    structuralComplete := by
      intro datum root fuel value represented
      apply base.structuralComplete datum root fuel value
      cases fuel <;>
        simpa only [ExposedValue.withIdentity, Tier1Structural.Node.representsAt] using represented }

public structure Mixed where
  number : Nat
  flag : Bool
  deriving SpytialReify

example : True := by
  fail_if_success have : Tier1Lossless Mixed := by spytial_lossless
  trivial

#eval show Lean.MetaM Unit from do
  let value := Mixed.mk 1 true
  if tier1Represents (Tier1.relationalizeCandidate value) value then
    throwError "cross-type collision fixture unexpectedly preserved structure"

end TypeCollision

-- These evaluations check sharing behavior; the round-trip claims above are universal proofs.
#eval show Lean.MetaM Unit from do
  let leaf := Tree.leaf 7
  let value := Tree.branch leaf leaf
  unless (Tier1.relationalizeCandidate value).data.atoms.size == 3 do
    throwError "derived losslessness changed structural sharing"
  let lossy := Lossy.next (.leaf 7)
  if tier1Represents (Tier1.relationalizeCandidate lossy) lossy then
    throwError "lossy identity fixture unexpectedly preserved structure"
  for name in #[``pair_roundTrip, ``tree_roundTrip, ``list_roundTrip, ``lists_roundTrip,
      ``mixed_roundTrip, ``unshared_roundTrip, ``Tier1.reify_relationalize_of_lossless] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected axiom in derived round trip: {name}: {axioms}"

end Tier1LosslessTest
