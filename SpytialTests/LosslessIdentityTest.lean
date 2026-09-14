module

public import SpytialLean.ReifyInstances
public import SpytialLean.LosslessIdentity
public import SpytialLean.ReconstructionInvariance
public meta import SpytialLean.LosslessIdentityDeriving
public meta import SpytialLean.ReifyInstances
public meta import Lean.Util.CollectAxioms

open SpytialLean

namespace LosslessIdentityTest

public structure Pair where
  left : Nat
  right : Nat
  deriving SpytialIdentity, SpytialReify, LosslessIdentity

public theorem pair_roundTrip (value : Pair) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

public inductive Tree where
  | leaf (value : Nat)
  | branch (left right : Tree)
  deriving SpytialIdentity, SpytialReify, LosslessIdentity

public theorem tree_roundTrip (value : Tree) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

-- These quantify over every tree, rather than checking one serialized example. Every structural
-- relation may share a display name, and a same-named observation may point at an unrelated value.
public theorem tree_sameName_roundTrip (value : Tree) :
    let datum := Structural.relationalizeCandidate value
    reify { datum with data.relations := datum.data.relations.map fun relation =>
      { relation with name := "value" } } = Except.ok value :=
  Structural.reify_relationalize_renameRelations value (fun _ => "value")

public theorem tree_observation_roundTrip (value : Tree) :
    let datum := Structural.relationalizeCandidate value
    let observation : JsonRelation :=
      { id := "observation", name := "value", types := #["Tree", "Tree"],
        tuples := #[{ atoms := #[datum.root, datum.root], types := #["Tree", "Tree"] }] }
    reify { datum with data.relations := datum.data.relations ++ #[observation] } =
      Except.ok value := by
  apply Structural.reify_relationalize_appendRelations value
  intro relation member type field
  simp only [List.mem_singleton] at member
  subst relation
  intro equal
  have different := congrArg (fun id : String => id.toList.head?) equal
  simp [fieldRelationId, String.toList_append] at different

public instance : LosslessIdentity (List Nat) := by spytial_lossless
public instance : LosslessIdentity (Option String) := by spytial_lossless
public instance : LosslessIdentity Int := by spytial_lossless
public instance : LosslessIdentity (Sum Nat String) := by spytial_lossless
public instance : LosslessIdentity PUnit := by spytial_lossless

public theorem list_roundTrip (value : List Nat) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

public structure Forest where
  left : Tree
  right : Tree
  deriving SpytialIdentity, SpytialReify, LosslessIdentity

public structure Lists where
  first : List Nat
  rest : List (List Nat)
  deriving SpytialReify, LosslessIdentity

public theorem lists_roundTrip (value : Lists) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

public inductive Empty where
  deriving SpytialIdentity, SpytialReify, LosslessIdentity

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
  deriving SpytialReify, LosslessIdentity

public theorem mixed_roundTrip (value : Mixed) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

end Instantiated

public inductive Unshared where
  | leaf (value : String)
  | next (child : Unshared)
  deriving SpytialReify

public instance : SpytialIdentity Unshared := SpytialIdentity.asWritten
deriving instance LosslessIdentity for Unshared

public theorem unshared_roundTrip (value : Unshared) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalize_of_lossless value

public inductive Lossy where
  | leaf (value : Nat)
  | next (child : Lossy)
  deriving SpytialReify

public instance : SpytialIdentity Lossy where
  via := .identity (fun _ => IdentityKey.ofNat 0)

example : True := by
  fail_if_success have : LosslessIdentity Lossy := by spytial_lossless
  trivial

namespace TypeCollision

-- Both selected value classifiers are injective, but the two types deliberately share a tag.
-- Certifying each type in isolation would miss the resulting cross-type merge.
local instance : StructuralExposure Bool :=
  let base : StructuralExposure Bool := inferInstance
  { base with
    typeKey := natTypeKey
    structuralComplete := by
      intro datum root fuel value represented
      apply base.structuralComplete datum root fuel value
      cases fuel <;>
        simpa only [ExposedValue.withIdentity, StructuralEncoding.Node.representsAt] using represented }

public structure Mixed where
  number : Nat
  flag : Bool
  deriving SpytialReify

example : True := by
  fail_if_success have : LosslessIdentity Mixed := by spytial_lossless
  trivial

#eval show Lean.MetaM Unit from do
  let value := Mixed.mk 1 true
  if structurallyRepresents (Structural.relationalizeCandidate value) value then
    throwError "cross-type collision fixture unexpectedly preserved structure"

end TypeCollision

-- These evaluations check sharing behavior; the round-trip claims above are universal proofs.
#eval show Lean.MetaM Unit from do
  let leaf := Tree.leaf 7
  let value := Tree.branch leaf leaf
  unless (Structural.relationalizeCandidate value).data.atoms.size == 3 do
    throwError "derived losslessness changed structural sharing"
  let lossy := Lossy.next (.leaf 7)
  if structurallyRepresents (Structural.relationalizeCandidate lossy) lossy then
    throwError "lossy identity fixture unexpectedly preserved structure"
  for name in #[``pair_roundTrip, ``tree_roundTrip, ``list_roundTrip, ``lists_roundTrip,
      ``mixed_roundTrip, ``unshared_roundTrip, ``tree_sameName_roundTrip,
      ``tree_observation_roundTrip, ``Structural.reify_relationalize_of_lossless,
      ``Structural.reify_relationalize_of_sameStructure] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected axiom in derived round trip: {name}: {axioms}"

end LosslessIdentityTest
