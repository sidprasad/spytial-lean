module

public import SpytialLean.StructuralExposure
public import SpytialLean.ReifyInstances
public meta import SpytialLean.ReifyInstances
public meta import SpytialLean.ReifyDeriving
public meta import Lean.Util.CollectAxioms
import all SpytialLean.Identity
import all SpytialLean.StructuralExposure
import all SpytialLean.StructuralSharing

open SpytialLean RelationalizerCore

namespace StructuralSharingTest

local instance : SpytialIdentity Nat where
  via := .identity ToIdentityKey.toKey

local instance : SpytialIdentity Bool where
  via := .identity ToIdentityKey.toKey

#eval show Lean.MetaM Unit from do
  for name in #[``StructuralEncoding.walk_sharing_represents,
      ``StructuralEncoding.walk_coherent_represents, ``Structural.reify_relationalizeCandidate,
      ``Structural.reify_relationalizeCandidate_of_coherent,
      ``Structural.reify_relationalizeCandidate_nat, ``Structural.reify_relationalizeCandidate_string] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "sharing theorem contains unexpected axioms: {name}: {axioms}"

example (value : Nat) : reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalizeCandidate_nat value

example (value : String) : reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalizeCandidate_string value

public structure Box (alpha : Type) where
  value : alpha
  deriving SpytialIdentity, SpytialReify

public structure Mixed where
  left : Box Nat
  right : Box Bool
  deriving SpytialReify

-- These value keys intentionally coincide. The instantiated type keys must separate them.
example : ValueIdentity.key? (⟨1⟩ : Box Nat) = ValueIdentity.key? (⟨true⟩ : Box Bool) := by
  rfl

#eval show Lean.MetaM Unit from do
  if StructuralExposure.typeKey (alpha := Box Nat) == StructuralExposure.typeKey (alpha := Box Bool) then
    throwError "instantiated type keys collided"
  let value := Mixed.mk ⟨1⟩ ⟨true⟩
  unless structurallyRepresents (Structural.relationalizeCandidate value) value do
    throwError "mixed instantiated types were merged"

public inductive Branch (alpha : Type) where
  | leaf (value : alpha)
  | branch (left right : Branch alpha)
  deriving SpytialIdentity, SpytialReify

public structure MixedRecursive where
  left : Branch Nat
  right : Branch Bool
  deriving SpytialReify

#eval show Lean.MetaM Unit from do
  let value : MixedRecursive :=
    ⟨.branch (.leaf 1) (.leaf 1), .branch (.leaf true) (.leaf true)⟩
  unless structurallyRepresents (Structural.relationalizeCandidate value) value do
    throwError "recursive occurrences omitted datatype arguments from their type keys"

public structure Pair where
  left : Nat
  right : Nat
  deriving SpytialIdentity, SpytialReify

-- A proof-only inverse of primitive keys. Neither the walker nor reify uses this function.
private noncomputable def natOfKey (key : IdentityKey) : Nat := by
  classical
  exact if h : ∃ n, IdentityKey.ofNat n = key then h.choose else 0

private theorem natOfKey_ofNat (n : Nat) : natOfKey (.ofNat n) = n := by
  have existsNat : ∃ m, IdentityKey.ofNat m = IdentityKey.ofNat n := ⟨n, rfl⟩
  unfold natOfKey
  rw [dif_pos existsNat]
  exact IdentityKey.ofNat_injective existsNat.choose_spec

private noncomputable def pairMeaning (value : Pair)
    (key : IdentityKey × IdentityKey) : Node IdentityKey IdentityKey :=
  if key.1 == natTypeKey then
    .value .asWritten "Nat" (natOfKey key.2).repr []
  else StructuralEncoding.Node.asWritten (StructuralExposure.nodeOf value)

private theorem nat_sound (value : Pair) (n : Nat) :
    StructuralEncoding.Node.IdentitySound (pairMeaning value) (StructuralExposure.nodeOf n) := by
  constructor
  · intro key found
    change some (natTypeKey, IdentityKey.ofNat n) = some key at found
    cases Option.some.inj found
    simp [pairMeaning, natOfKey_ofNat, StructuralExposure.expose, StructuralEncoding.Node.asWritten,
      StructuralEncoding.Node.asWrittenFields]
  · trivial

private theorem pair_sound (value : Pair) :
    StructuralEncoding.Node.IdentitySound (pairMeaning value) (StructuralExposure.nodeOf value) := by
  rcases value with ⟨left, right⟩
  constructor
  · intro key found
    change StructuralEncoding.Node.key?
      (.value (valueIdentity (IdentityKey.ofString "StructuralSharingTest.Pair") (Pair.mk left right))
        "Pair" "mk" _) = some key at found
    cases selected : ValueIdentity.key? (Pair.mk left right) with
    | none => simp [valueIdentity, selected, StructuralEncoding.Node.key?] at found
    | some valueKey =>
        simp only [valueIdentity, selected, StructuralEncoding.Node.key?] at found
        cases Option.some.inj found
        simp [pairMeaning, natTypeKey, StructuralExposure.nodeOf, ExposedValue.withIdentity]
  · exact ⟨nat_sound _ left, nat_sound _ right, trivial⟩

-- A genuine universal equality for the unchecked shared engine, including equal children.
-- There is no per-value computation, native_decide, representation test, or identity fallback.
public theorem pair_roundTrip (value : Pair) :
    reify (Structural.relationalizeCandidate value) = Except.ok value :=
  Structural.reify_relationalizeCandidate_of_coherent value (pair_sound value).coherent

#eval show Lean.MetaM Unit from do
  unless (Structural.relationalizeCandidate (Pair.mk 7 7)).data.atoms.size == 2 do
    throwError "equal children did not share an atom"
  unless (Structural.relationalizeCandidate (Pair.mk 7 8)).data.atoms.size == 3 do
    throwError "unequal children were merged"
  let axioms ← Lean.collectAxioms ``pair_roundTrip
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "pair round-trip theorem contains unexpected axioms: {axioms}"

-- Exercise the generic proof on arbitrary finite recursive structures, with subtree equality
-- as identity. Keys live only in the engine's interning table, never in the emitted datum.
public inductive TreeKey where
  | tip (value : Nat)
  | fork (left right : TreeKey)
  deriving BEq, ReflBEq, LawfulBEq, Hashable

public def treeNode : TreeKey → Node Unit TreeKey
  | .tip n => .value (.keyed () (.tip n)) "Tree" n.repr []
  | .fork left right => .value (.keyed () (.fork left right)) "Tree" "fork"
      [("left", treeNode left), ("right", treeNode right)]

private theorem tree_wellFormed (tree : TreeKey) :
    StructuralEncoding.Node.WellFormed (treeNode tree) := by
  induction tree <;>
    simp_all [treeNode, StructuralEncoding.Node.WellFormed, StructuralEncoding.Node.FieldsWellFormed]

private theorem tree_sound (tree : TreeKey) :
    StructuralEncoding.Node.IdentitySound
      (fun key => StructuralEncoding.Node.asWritten (treeNode key.2)) (treeNode tree) := by
  induction tree with
  | tip n =>
      constructor
      · intro key found
        change some ((), TreeKey.tip n) = some key at found
        cases Option.some.inj found
        rfl
      · trivial
  | fork left right leftIH rightIH =>
      constructor
      · intro key found
        change some ((), TreeKey.fork left right) = some key at found
        cases Option.some.inj found
        rfl
      · exact ⟨leftIH, rightIH, trivial⟩

public theorem recursive_sharing_preserves (tree : TreeKey) :
    let datum := walk (treeNode tree)
    StructuralEncoding.Node.representsAt datum.data datum.root (datum.data.atoms.size + 1)
      (treeNode tree) = true :=
  StructuralEncoding.walk_sharing_represents _ _ (tree_wellFormed tree) (tree_sound tree)

#eval show Lean.MetaM Unit from do
  let repeated := TreeKey.fork (.tip 7) (.tip 7)
  unless (walk (treeNode (.fork repeated repeated))).data.atoms.size == 3 do
    throwError "recursive sharing was lost"
  let axioms ← Lean.collectAxioms ``recursive_sharing_preserves
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "recursive sharing theorem contains unexpected axioms: {axioms}"

private def badLeaf : Node Unit Nat := .value (.keyed () 0) "T" "leaf" []
private def badParent : Node Unit Nat :=
  .value (.keyed () 0) "T" "parent" [("child", badLeaf)]

-- Reusing an unfinished ancestor is precisely the kind of policy excluded by coherence.
example : ¬ StructuralEncoding.Node.Coherent badParent := by
  intro coherent
  have same := coherent badParent badLeaf ((), 0) .here
    (.field (name := "child") (by simp) .here) rfl rfl
  simp [badParent, badLeaf, StructuralEncoding.Node.asWritten,
    StructuralEncoding.Node.asWrittenFields] at same

end StructuralSharingTest
