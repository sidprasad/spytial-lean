module

public import SpytialLean.ReifyCore
public import SpytialLean.RelationalizerCore
import Std.Data.HashMap.Lemmas
import Std.Data.String.ToNat

namespace SpytialLean.Tier1Structural

open SpytialLean.RelationalizerCore

/-!
# Generic occurrence-preserving relationalization theorem

This module proves that the existing `RelationalizerCore.Engine` represents every well-formed
structural node when identity is set to `asWritten`. The small `Graph.addFreshNode` traversal below
is a proof specification, not a second public relationalizer: `Engine.addNode_asWritten` proves that
the production engine computes exactly that traversal, and the exported theorem is stated directly
about `RelationalizerCore.relationalize`.

The proof accounts for generated atom IDs, atom and relation lookup, unique field ownership,
relation accumulation, recursion fuel, and preservation of earlier graph entries. The public API is
the node interpretation, its well-formedness condition, identity erasure, and the final theorem.
-/

theorem filter_key_eq_singleton {α β : Type} [BEq β] [LawfulBEq β]
    (key : α → β) (xs : List α) (x : α)
    (nodup : (xs.map key).Nodup) (mem : x ∈ xs) :
    xs.filter (fun y => key y == key x) = [x] := by
  induction xs with
  | nil => simp at mem
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at nodup
      rcases nodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons] at mem
      rcases mem with rfl | tailMem
      · simp only [beq_self_eq_true, List.filter_cons_of_pos]
        have noMatch : tail.filter (fun y => key y == key x) = [] := by
          rw [List.filter_eq_nil_iff]
          intro y yMem
          simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
          intro equal
          apply headFresh
          rw [← equal]
          exact List.mem_map_of_mem yMem
        simp [noMatch]
      · have keyNe : key head ≠ key x := by
          intro equal
          apply headFresh
          rw [equal]
          exact List.mem_map_of_mem tailMem
        simp [keyNe, ih tailNodup tailMem]

theorem atom_ok_of_mem {datum : JsonDataInstance} {atom : JsonAtom}
    (nodup : (datum.atoms.toList.map JsonAtom.id).Nodup)
    (mem : atom ∈ datum.atoms.toList) :
    datum.atom atom.id = .ok atom := by
  unfold JsonDataInstance.atom
  rw [filter_key_eq_singleton JsonAtom.id datum.atoms.toList atom nodup mem]

private def relationOfEntry (entry : String × (Array String × Array JsonTuple)) : JsonRelation :=
  { id := entry.1, name := entry.1, types := entry.2.1, tuples := entry.2.2 }

theorem relation_filter_of_get {graph : Graph} {name : String}
    {types : Array String} {tuples : Array JsonTuple}
    (found : graph.relations[name]? = some (types, tuples)) :
    (graph.toDataInstance.relations.toList.filter (fun relation => relation.name == name)) =
      [{ id := name, name, types, tuples }] := by
  have member : (name, (types, tuples)) ∈ graph.relations.toList := by
    simpa [Std.HashMap.mem_toList_iff_getElem?_eq_some] using found
  have nodup : (graph.relations.toList.map fun entry => entry.1).Nodup := by
    simpa [Std.HashMap.map_fst_toList_eq_keys] using graph.relations.nodup_keys
  have filtered := filter_key_eq_singleton (fun entry => entry.1)
    graph.relations.toList (name, (types, tuples)) nodup member
  simp only [Graph.toDataInstance, Array.toList_map, Std.HashMap.toList_toArray]
  change (List.map relationOfEntry graph.relations.toList).filter
    (fun relation => relation.name == name) = [_]
  rw [List.filter_map]
  change List.map relationOfEntry
    (graph.relations.toList.filter (fun entry => entry.1 == name)) = [_]
  rw [filtered]
  rfl

theorem child_ok_of_mem {graph : Graph}
    {owner child field ownerType childType ownerLabel childLabel : String}
    {declaredTypes : Array String} {tuples : Array JsonTuple}
    (atomNodup : (graph.atoms.toList.map JsonAtom.id).Nodup)
    (ownerMem : { id := owner, type := ownerType, label := ownerLabel } ∈ graph.atoms.toList)
    (childMem : { id := child, type := childType, label := childLabel } ∈ graph.atoms.toList)
    (relationFound : graph.relations[field]? = some (declaredTypes, tuples))
    (ownerNodup : (tuples.toList.map fun tuple => tuple.atoms[0]?).Nodup)
    (tupleMem : { atoms := #[owner, child], types := #[ownerType, childType] } ∈ tuples.toList) :
    graph.toDataInstance.child owner field = .ok child := by
  have ownerOk : graph.toDataInstance.atom owner =
      .ok { id := owner, type := ownerType, label := ownerLabel } :=
    by simpa [Graph.toDataInstance] using
      atom_ok_of_mem (datum := graph.toDataInstance) atomNodup ownerMem
  have childOk : graph.toDataInstance.atom child =
      .ok { id := child, type := childType, label := childLabel } :=
    by simpa [Graph.toDataInstance] using
      atom_ok_of_mem (datum := graph.toDataInstance) atomNodup childMem
  have relationFilter := relation_filter_of_get relationFound
  have tupleFilter := filter_key_eq_singleton (fun tuple => tuple.atoms[0]?)
    tuples.toList { atoms := #[owner, child], types := #[ownerType, childType] }
    ownerNodup tupleMem
  have tupleFilter' : tuples.toList.filter (fun tuple => tuple.atoms[0]? == some owner) =
      [{ atoms := #[owner, child], types := #[ownerType, childType] }] := by
    simpa using tupleFilter
  unfold JsonDataInstance.child
  simp_all [Bind.bind, Pure.pure, Except.bind, Except.pure]

namespace Node

mutual
  @[expose] public def asWritten : Node typeKey valueKey → Node typeKey valueKey
    | .value _ type label fields => .value .asWritten type label (asWrittenFields fields)

  @[expose] public def asWrittenFields : List (String × Node typeKey valueKey) →
      List (String × Node typeKey valueKey)
    | [] => []
    | (name, child) :: fields => (name, asWritten child) :: asWrittenFields fields
end

mutual
  def depth : Node typeKey valueKey → Nat
    | .value _ _ _ fields => depthFields fields + 1

  def depthFields : List (String × Node typeKey valueKey) → Nat
    | [] => 0
    | (_, child) :: fields => max (depth child) (depthFields fields)
end

mutual
  def count : Node typeKey valueKey → Nat
    | .value _ _ _ fields => countFields fields + 1

  def countFields : List (String × Node typeKey valueKey) → Nat
    | [] => 0
    | (_, child) :: fields => count child + countFields fields + 1
end

mutual
  def atomCount : Node typeKey valueKey → Nat
    | .value _ _ _ fields => atomCountFields fields + 1

  def atomCountFields : List (String × Node typeKey valueKey) → Nat
    | [] => 0
    | (_, child) :: fields => atomCount child + atomCountFields fields
end

mutual
  theorem depth_le_atomCount (node : Node typeKey valueKey) :
      depth node ≤ atomCount node := by
    cases node with
    | value identity type label fields =>
        simp only [depth, atomCount]
        exact Nat.add_le_add_right (depthFields_le_atomCountFields fields) 1

  theorem depthFields_le_atomCountFields
      (fields : List (String × Node typeKey valueKey)) :
      depthFields fields ≤ atomCountFields fields := by
    cases fields with
    | nil => simp [depthFields, atomCountFields]
    | cons field fields =>
        rcases field with ⟨name, child⟩
        simp only [depthFields, atomCountFields]
        have childLe := depth_le_atomCount child
        have fieldsLe := depthFields_le_atomCountFields fields
        exact Nat.max_le.mpr ⟨by omega, by omega⟩
end

def fieldNames : Node typeKey valueKey → List String
  | .value _ _ _ fields => fields.map Prod.fst

mutual
  @[expose] public def WellFormed : Node typeKey valueKey → Prop
    | .value _ _ _ fields => FieldsWellFormed fields

  @[expose] public def FieldsWellFormed : List (String × Node typeKey valueKey) → Prop
    | [] => True
    | (name, child) :: fields =>
        name ∉ fields.map Prod.fst ∧ WellFormed child ∧ FieldsWellFormed fields
end

@[expose] public def representsAt (datum : JsonDataInstance) (root : String) :
    Nat → Node typeKey valueKey → Bool
  | 0, _ => false
  | fuel + 1, .value _ type label fields =>
      datum.constructorRepresents root type label <|
        fields.all fun (name, child) =>
          datum.childRepresentsWith root name
            (fun childRoot _ => representsAt datum childRoot fuel child) child
termination_by fuel => fuel

end Node

def atomId (index : Nat) : String := s!"atom_{index}"

theorem atomId_injective : Function.Injective atomId := by
  intro left right equality
  apply (Nat.repr_inj).mp
  exact (String.append_right_inj "atom_").mp equality

def tupleOwner? (tuple : JsonTuple) : Option String := tuple.atoms[0]?

def fieldTuple (owner child ownerType childType : String) : JsonTuple :=
  { atoms := #[owner, child], types := #[ownerType, childType] }

theorem arrayPair_head (first second : String) :
    (#[first, second] : Array String)[0]? = some first := by
  rfl

structure Graph.Valid (graph : Graph) : Prop where
  atomIdsNodup : (graph.atoms.toList.map JsonAtom.id).Nodup
  atomIdsBelow : ∀ atom ∈ graph.atoms.toList,
    ∃ index, index < graph.nextId ∧ atom.id = atomId index
  relationOwnersNodup : ∀ (name : String) (types : Array String) (tuples : Array JsonTuple),
    graph.relations[name]? = some (types, tuples) →
      (tuples.toList.map tupleOwner?).Nodup
  relationOwnersBelow : ∀ (name : String) (types : Array String) (tuples : Array JsonTuple)
      (owner : String),
    graph.relations[name]? = some (types, tuples) →
      some owner ∈ tuples.toList.map tupleOwner? →
      ∃ index, index < graph.nextId ∧ owner = atomId index

def Graph.allocateAtom (graph : Graph) (type label : String) : String × Graph :=
  let (id, graph) := graph.freshId
  (id, graph.addAtom { id, type, label })

theorem Graph.Valid.empty : Valid ({} : Graph) := by
  constructor <;> simp

theorem Graph.Valid.allocateAtom (valid : Valid graph) :
    let (id, larger) := allocateAtom graph type label
    Valid larger ∧
      { id, type, label } ∈ larger.atoms.toList ∧
      (∀ atom, atom ∈ graph.atoms.toList → atom ∈ larger.atoms.toList) ∧
      larger.nextId = graph.nextId + 1 ∧
      larger.atoms.size = graph.atoms.size + 1 := by
  dsimp [Graph.allocateAtom, Graph.freshId, Graph.addAtom]
  have fresh : s!"atom_{graph.nextId}" ∉ graph.atoms.toList.map JsonAtom.id := by
    intro member
    rcases List.mem_map.mp member with ⟨atom, atomMem, atomIdEq⟩
    rcases valid.atomIdsBelow atom atomMem with ⟨index, indexLt, oldId⟩
    have : index = graph.nextId := atomId_injective (oldId.symm.trans atomIdEq)
    omega
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have appended :
          (graph.atoms.toList.map JsonAtom.id ++ [s!"atom_{graph.nextId}"]).Nodup := by
          rw [List.nodup_append]
          refine ⟨valid.atomIdsNodup, by simp, ?_⟩
          intro old oldMem new newMem
          simp only [List.mem_singleton] at newMem
          subst new
          exact fun equal => fresh (by simpa [equal] using oldMem)
      simpa [Array.toList_push, List.concat_eq_append] using appended
    · intro atom atomMem
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at atomMem
      rcases atomMem with atomMem | rfl
      · rcases valid.atomIdsBelow atom atomMem with ⟨index, indexLt, idEq⟩
        change ∃ index, index < graph.nextId + 1 ∧ atom.id = atomId index
        exact ⟨index, by omega, idEq⟩
      · change ∃ index, index < graph.nextId + 1 ∧
          s!"atom_{graph.nextId}" = atomId index
        exact ⟨graph.nextId, by omega, rfl⟩
    · simpa using valid.relationOwnersNodup
    · intro name types tuples owner found ownerMem
      rcases valid.relationOwnersBelow name types tuples owner found ownerMem with
        ⟨index, indexLt, ownerEq⟩
      change ∃ index, index < graph.nextId + 1 ∧ owner = atomId index
      exact ⟨index, by omega, ownerEq⟩
  · refine ⟨?_, ?_, rfl, by simp⟩
    · simp [Array.toList_push]
    intro atom atomMem
    simp [Array.toList_push, atomMem]

theorem Graph.addField_get_self (graph : Graph)
    (name owner ownerType child childType : String) :
    let existing := graph.relations.getD name (#[ownerType, childType], #[])
    (graph.addField name owner ownerType child childType).relations[name]? =
      some (existing.1, existing.2.push {
        atoms := #[owner, child], types := #[ownerType, childType] }) := by
  simp [Graph.addField, Graph.addTuple]

theorem Graph.addField_get_other (graph : Graph)
    {other name owner ownerType child childType : String} (different : name ≠ other) :
    (graph.addField name owner ownerType child childType).relations[other]? =
      graph.relations[other]? := by
  simp [Graph.addField, Graph.addTuple, Std.HashMap.getElem?_insert, different]

def Graph.OwnerFree (graph : Graph) (owner : String) : Prop :=
  ∀ (name : String) (types : Array String) (tuples : Array JsonTuple),
    graph.relations[name]? = some (types, tuples) →
    some owner ∉ tuples.toList.map tupleOwner?

def Graph.FieldFree (graph : Graph) (owner name : String) : Prop :=
  ∀ (types : Array String) (tuples : Array JsonTuple),
    graph.relations[name]? = some (types, tuples) →
      some owner ∉ tuples.toList.map tupleOwner?

def Graph.Subgraph (smaller larger : Graph) : Prop :=
  (∀ atom, atom ∈ smaller.atoms.toList → atom ∈ larger.atoms.toList) ∧
  ∀ (name : String) (types : Array String) (tuples : Array JsonTuple)
      (tuple : JsonTuple),
    smaller.relations[name]? = some (types, tuples) → tuple ∈ tuples.toList →
      ∃ largerTypes largerTuples,
        larger.relations[name]? = some (largerTypes, largerTuples) ∧
        tuple ∈ largerTuples.toList

theorem Graph.FieldFree.allocateAtom (free : FieldFree graph owner name) :
    let (_, larger) := allocateAtom graph type label
    FieldFree larger owner name := by
  unfold FieldFree at *
  simpa [SpytialLean.Tier1Structural.Graph.allocateAtom, Graph.freshId, Graph.addAtom] using free

theorem Graph.Valid.allocateAtom_ownerFree (valid : Valid graph) :
    let (owner, larger) := SpytialLean.Tier1Structural.Graph.allocateAtom graph type label
    OwnerFree larger owner := by
  dsimp [SpytialLean.Tier1Structural.Graph.allocateAtom, Graph.freshId, Graph.addAtom, OwnerFree]
  intro name types tuples found ownerMem
  rcases valid.relationOwnersBelow name types tuples (atomId graph.nextId) found ownerMem with
    ⟨index, indexLt, ownerEq⟩
  have : graph.nextId = index := atomId_injective ownerEq
  omega

theorem Graph.FieldFree.addField_of_name_ne (free : FieldFree graph protectedOwner target)
    (different : addedName ≠ target) :
    FieldFree (graph.addField addedName owner ownerType child childType) protectedOwner target := by
  intro types tuples found
  apply free types tuples
  rw [← found]
  exact (addField_get_other graph different).symm

theorem Graph.FieldFree.addField_of_owner_ne (free : FieldFree graph protectedOwner target)
    (different : owner ≠ protectedOwner) :
    FieldFree (graph.addField addedName owner ownerType child childType) protectedOwner target := by
  by_cases same : addedName = target
  · subst target
    intro types tuples found
    cases oldFound : graph.relations[addedName]? with
    | none =>
        have self := addField_get_self graph addedName owner ownerType child childType
        rw [Std.HashMap.getD_eq_getD_getElem?, oldFound] at self
        simp at self
        have pairEq := Option.some.inj (found.symm.trans self)
        cases pairEq
        simp only [List.map_singleton, List.mem_singleton, tupleOwner?]
        intro member
        rw [arrayPair_head] at member
        exact different (Option.some.inj member).symm
    | some old =>
        rcases old with ⟨oldTypes, oldTuples⟩
        have self := addField_get_self graph addedName owner ownerType child childType
        rw [Std.HashMap.getD_eq_getD_getElem?, oldFound] at self
        simp at self
        have pairEq := Option.some.inj (found.symm.trans self)
        cases pairEq
        have oldFree := free types oldTuples oldFound
        simp only [Array.toList_push, List.map_append, List.map_singleton,
          List.mem_append, List.mem_singleton, tupleOwner?]
        intro member
        rcases member with oldMember | newMember
        · exact oldFree oldMember
        · rw [arrayPair_head] at newMember
          exact different (Option.some.inj newMember).symm
  · exact free.addField_of_name_ne same

theorem Graph.Valid.addField (valid : Valid graph)
    (fieldFree : FieldFree graph owner name)
    (ownerMem : { id := owner, type := ownerType, label := ownerLabel } ∈ graph.atoms.toList) :
    Valid (graph.addField name owner ownerType child childType) := by
  have ownerBelow : ∃ index, index < graph.nextId ∧ owner = atomId index := by
    rcases valid.atomIdsBelow _ ownerMem with ⟨index, indexLt, idEq⟩
    change owner = atomId index at idEq
    exact ⟨index, indexLt, idEq⟩
  have ownerBelow' : ∃ index,
      index < (graph.addField name owner ownerType child childType).nextId ∧
        owner = atomId index := by
    simpa [Graph.addField, Graph.addTuple] using ownerBelow
  refine ⟨valid.atomIdsNodup, valid.atomIdsBelow, ?_, ?_⟩
  · intro other types tuples found
    by_cases same : name = other
    · subst other
      cases oldFound : graph.relations[name]? with
      | none =>
          have self := addField_get_self graph name owner ownerType child childType
          rw [Std.HashMap.getD_eq_getD_getElem?, oldFound] at self
          simp at self
          have pairEq := Option.some.inj (found.symm.trans self)
          cases pairEq
          simp [tupleOwner?]
      | some old =>
          rcases old with ⟨oldTypes, oldTuples⟩
          have self := addField_get_self graph name owner ownerType child childType
          rw [Std.HashMap.getD_eq_getD_getElem?, oldFound] at self
          simp at self
          have pairEq := Option.some.inj (found.symm.trans self)
          cases pairEq
          have oldNodup := valid.relationOwnersNodup name types oldTuples oldFound
          have oldFree := fieldFree types oldTuples oldFound
          rw [Array.toList_push, List.map_append, List.map_singleton,
            List.nodup_append]
          refine ⟨oldNodup, by simp, ?_⟩
          intro old oldMember new newMember
          simp only [tupleOwner?, List.mem_singleton] at newMember
          subst new
          exact fun equal => oldFree (by simpa [equal] using oldMember)
    · have oldFound : graph.relations[other]? = some (types, tuples) := by
        rw [← found]
        exact (addField_get_other graph same).symm
      exact valid.relationOwnersNodup other types tuples oldFound
  · intro other types tuples queriedOwner found queriedOwnerMem
    by_cases same : name = other
    · subst other
      cases oldFound : graph.relations[name]? with
      | none =>
          have self := addField_get_self graph name owner ownerType child childType
          rw [Std.HashMap.getD_eq_getD_getElem?, oldFound] at self
          simp at self
          have pairEq := Option.some.inj (found.symm.trans self)
          cases pairEq
          simp [tupleOwner?] at queriedOwnerMem
          subst queriedOwner
          exact ownerBelow'
      | some old =>
          rcases old with ⟨oldTypes, oldTuples⟩
          have self := addField_get_self graph name owner ownerType child childType
          rw [Std.HashMap.getD_eq_getD_getElem?, oldFound] at self
          simp at self
          have pairEq := Option.some.inj (found.symm.trans self)
          cases pairEq
          simp only [Array.toList_push, List.map_append, List.map_singleton,
            List.mem_append, List.mem_singleton, tupleOwner?] at queriedOwnerMem
          rcases queriedOwnerMem with oldMember | newMember
          · simpa [Graph.addField, Graph.addTuple] using
              valid.relationOwnersBelow name types oldTuples queriedOwner
                oldFound oldMember
          · rw [arrayPair_head] at newMember
            have queriedEq : queriedOwner = owner := Option.some.inj newMember
            simpa [queriedEq] using ownerBelow'
    · have oldFound : graph.relations[other]? = some (types, tuples) := by
        rw [← found]
        exact (addField_get_other graph same).symm
      simpa [Graph.addField, Graph.addTuple] using
        valid.relationOwnersBelow other types tuples queriedOwner oldFound queriedOwnerMem

def nodeTypeName : Node typeKey valueKey → String
  | .value _ type _ _ => type

def Graph.HasId (graph : Graph) (id : String) : Prop :=
  ∃ atom, atom ∈ graph.atoms.toList ∧ atom.id = id

theorem Graph.Subgraph.hasId {id : String} (subgraph : Subgraph smaller larger) :
    SpytialLean.Tier1Structural.Graph.HasId smaller id →
      SpytialLean.Tier1Structural.Graph.HasId larger id := by
  rintro ⟨atom, atomMem, atomIdEq⟩
  exact ⟨atom, subgraph.1 atom atomMem, atomIdEq⟩

theorem Graph.Valid.oldId_ne_fresh {id : String} (valid : Valid graph)
    (old : SpytialLean.Tier1Structural.Graph.HasId graph id) :
    id ≠ atomId graph.nextId := by
  rintro equality
  rcases old with ⟨atom, atomMem, atomIdEq⟩
  rcases valid.atomIdsBelow atom atomMem with ⟨index, indexLt, belowEq⟩
  have : index = graph.nextId := atomId_injective (belowEq.symm.trans (atomIdEq.trans equality))
  omega

theorem Graph.addField_contains (graph : Graph)
    (name owner ownerType child childType : String) :
    ∃ types tuples,
      (graph.addField name owner ownerType child childType).relations[name]? =
        some (types, tuples) ∧
      fieldTuple owner child ownerType childType ∈ tuples.toList := by
  let existing := graph.relations.getD name (#[ownerType, childType], #[])
  refine ⟨existing.1, existing.2.push (fieldTuple owner child ownerType childType), ?_, ?_⟩
  · simpa [existing, fieldTuple] using
      addField_get_self graph name owner ownerType child childType
  · simp [Array.toList_push]

mutual
  /- A proof-only specification for the occurrence-preserving behavior of the shared engine. -/
  def Graph.addFreshNode (graph : Graph) :
      Node typeKey valueKey → String × Graph
    | .value _ type label fields =>
        let (root, graph) := SpytialLean.Tier1Structural.Graph.allocateAtom graph type label
        (root, SpytialLean.Tier1Structural.Graph.addFreshFields graph root type fields)

  def Graph.addFreshFields (graph : Graph) (owner ownerType : String) :
      List (String × Node typeKey valueKey) → Graph
    | [] => graph
    | (name, child) :: fields =>
        let (childRoot, graph) := SpytialLean.Tier1Structural.Graph.addFreshNode graph child
        let graph := graph.addField name owner ownerType childRoot (nodeTypeName child)
        SpytialLean.Tier1Structural.Graph.addFreshFields graph owner ownerType fields
end

mutual
  inductive Graph.Encodes {typeKey : Type u} {valueKey : Type v} (graph : Graph) :
      String → Node typeKey valueKey → Prop where
    | value
        (atomMem : { id := root, type, label } ∈ graph.atoms.toList)
        (fieldsEncoded : EncodesFields graph root type fields) :
        Encodes graph root (.value identity type label fields)

  inductive Graph.EncodesFields {typeKey : Type u} {valueKey : Type v} (graph : Graph) :
      String → String → List (String × Node typeKey valueKey) → Prop where
    | nil : EncodesFields graph root ownerType []
    | cons
        (relationFound : graph.relations[name]? = some (declaredTypes, tuples))
        (tupleMem : fieldTuple root childRoot ownerType (nodeTypeName child) ∈ tuples.toList)
        (childEncoded : Encodes graph childRoot child)
        (fieldsEncoded : EncodesFields graph root ownerType fields) :
        EncodesFields graph root ownerType ((name, child) :: fields)
end

theorem Node.count_lt_countFields_cons (name : String) (child : Node typeKey valueKey)
    (fields : List (String × Node typeKey valueKey)) :
    count child < countFields ((name, child) :: fields) := by
  simp [countFields]
  omega

theorem Node.countFields_lt_countFields_cons (name : String) (child : Node typeKey valueKey)
    (fields : List (String × Node typeKey valueKey)) :
    countFields fields < countFields ((name, child) :: fields) := by
  simp [countFields]
  omega

theorem Graph.Subgraph.refl (graph : Graph) : Subgraph graph graph := by
  exact ⟨fun _ => id, fun _ types tuples tuple found member =>
    ⟨types, tuples, found, member⟩⟩

theorem Graph.Subgraph.trans (first : Subgraph small middle) (second : Subgraph middle large) :
    Subgraph small large := by
  constructor
  · intro atom member
    exact second.1 atom (first.1 atom member)
  · intro name types tuples tuple found member
    rcases first.2 name types tuples tuple found member with
      ⟨middleTypes, middleTuples, middleFound, middleMember⟩
    exact second.2 name middleTypes middleTuples tuple middleFound middleMember

theorem Graph.Subgraph.allocateAtom :
    let (_, larger) := allocateAtom graph type label
    Subgraph graph larger := by
  dsimp [allocateAtom, Graph.freshId, Graph.addAtom, Subgraph]
  constructor
  · intro atom member
    change atom ∈ graph.atoms.toList.concat _
    simp [List.concat_eq_append, member]
  · intro name types tuples tuple found member
    exact ⟨types, tuples, found, member⟩

theorem Graph.Subgraph.addField :
    Subgraph graph (graph.addField name owner ownerType child childType) := by
  constructor
  · intro atom member
    exact member
  · intro other types tuples tuple found member
    by_cases same : name = other
    · subst other
      let newTuple : JsonTuple := {
        atoms := #[owner, child], types := #[ownerType, childType] }
      have existingEq : graph.relations.getD name (#[ownerType, childType], #[]) =
          (types, tuples) := by
        rw [Std.HashMap.getD_eq_getD_getElem?, found]
        rfl
      refine ⟨types, tuples.push newTuple, ?_, ?_⟩
      · simpa [existingEq] using
          addField_get_self graph name owner ownerType child childType
      · simp [Array.toList_push, member]
    · exact ⟨types, tuples, (addField_get_other graph same).trans found, member⟩

mutual
theorem Graph.Encodes.mono (subgraph : Subgraph small large) :
    Encodes small root node → Encodes large root node := by
  intro encoded
  cases encoded with
  | value atomMem fieldsEncoded =>
      exact .value (subgraph.1 _ atomMem) (EncodesFields.mono subgraph fieldsEncoded)
  termination_by _ => Node.count node
  decreasing_by simp_all [Node.count] <;> omega

theorem Graph.EncodesFields.mono (subgraph : Subgraph small large) :
    EncodesFields small root ownerType fields → EncodesFields large root ownerType fields := by
  intro encoded
  cases encoded with
  | nil => exact .nil
  | @cons name declaredTypes tuples _ childRoot _ _ _ found tupleMem childEncoded
      fieldsEncoded =>
      rcases subgraph.2 name declaredTypes tuples _ found tupleMem with
        ⟨largeTypes, largeTuples, largeFound, largeTupleMem⟩
      exact .cons largeFound largeTupleMem (Encodes.mono subgraph childEncoded)
        (EncodesFields.mono subgraph fieldsEncoded)
  termination_by _ => Node.countFields fields
  decreasing_by
    all_goals
      simp only [Node.countFields]
      omega
end

mutual
  theorem Graph.Encodes.representsAt
      {typeKey : Type u} {valueKey : Type v} {graph : Graph} {root : String}
      {node : Node typeKey valueKey} {fuel : Nat}
      (valid : Valid graph) (encoded : Encodes graph root node)
      (enoughFuel : Node.depth node ≤ fuel) :
      Node.representsAt graph.toDataInstance root fuel node = true := by
    cases node with
    | value identity type label fields =>
        cases encoded with
        | value atomMem fieldsEncoded =>
            cases fuel with
            | zero => simp [Node.depth] at enoughFuel
            | succ fuel =>
                have ownerOk : graph.toDataInstance.atom root =
                    .ok { id := root, type, label } := by
                  simpa [Graph.toDataInstance] using
                    atom_ok_of_mem (datum := graph.toDataInstance)
                      valid.atomIdsNodup atomMem
                have fieldsEnough : Node.depthFields fields ≤ fuel := by
                  simpa [Node.depth] using enoughFuel
                have fieldsRepresent :=
                  EncodesFields.representsAt valid atomMem fieldsEncoded fieldsEnough
                simp_all [Node.representsAt, JsonDataInstance.constructorRepresents,
                  JsonDataInstance.expectAtom, Bind.bind, Pure.pure, Except.bind, Except.pure]

  theorem Graph.EncodesFields.representsAt
      {typeKey : Type u} {valueKey : Type v} {graph : Graph}
      {root ownerType ownerLabel : String}
      {fields : List (String × Node typeKey valueKey)} {fuel : Nat}
      (valid : Valid graph)
      (ownerMem : { id := root, type := ownerType, label := ownerLabel } ∈ graph.atoms.toList)
      (encoded : EncodesFields graph root ownerType fields)
      (enoughFuel : Node.depthFields fields ≤ fuel) :
      fields.all (fun (name, child) =>
        graph.toDataInstance.childRepresentsWith root name
          (fun childRoot (_ : Node typeKey valueKey) =>
            Node.representsAt graph.toDataInstance childRoot fuel child) child) =
        true := by
    cases fields with
    | nil => simp
    | cons field fields =>
        rcases field with ⟨name, child⟩
        cases encoded with
        | @cons _ declaredTypes tuples _ childRoot _ _ _ relationFound tupleMem
            childEncoded fieldsEncoded =>
            cases child with
            | value childIdentity childType childLabel childFields =>
                cases childEncoded with
                | value childMem childFieldsEncoded =>
                    have childOk : graph.toDataInstance.child root name = .ok childRoot :=
                      child_ok_of_mem valid.atomIdsNodup ownerMem childMem relationFound
                        (valid.relationOwnersNodup name declaredTypes tuples relationFound) tupleMem
                    have childEnough : Node.depth
                        (.value childIdentity childType childLabel childFields) ≤ fuel := by
                      simpa [Node.depthFields] using Nat.le_trans (Nat.le_max_left _ _) enoughFuel
                    have tailEnough : Node.depthFields fields ≤ fuel := by
                      exact Nat.le_trans (Nat.le_max_right _ _) enoughFuel
                    have childRepresents := Encodes.representsAt valid
                      (.value childMem childFieldsEncoded) childEnough
                    have fieldsRepresent :=
                      EncodesFields.representsAt valid ownerMem fieldsEncoded tailEnough
                    simp_all [JsonDataInstance.childRepresentsWith]
end

def Graph.PreservesOldFieldFree (before after : Graph) : Prop :=
  ∀ (owner name : String), SpytialLean.Tier1Structural.Graph.HasId before owner →
    FieldFree before owner name → FieldFree after owner name

mutual
  theorem Graph.addFreshNode_correct
      {typeKey : Type u} {valueKey : Type v} {graph : Graph}
      {node : Node typeKey valueKey}
      (valid : Valid graph) (wellFormed : Node.WellFormed node) :
      let (root, after) := SpytialLean.Tier1Structural.Graph.addFreshNode graph node
      Valid after ∧ Subgraph graph after ∧ Encodes after root node ∧
        after.atoms.size = graph.atoms.size + Node.atomCount node ∧
        PreservesOldFieldFree graph after := by
    cases node with
    | value identity type label fields =>
        change Node.FieldsWellFormed fields at wellFormed
        unfold SpytialLean.Tier1Structural.Graph.addFreshNode
        generalize allocation :
          SpytialLean.Tier1Structural.Graph.allocateAtom graph type label = allocated
        rcases allocated with ⟨root, afterAtom⟩
        have allocationFacts := valid.allocateAtom (type := type) (label := label)
        rw [allocation] at allocationFacts
        rcases allocationFacts with
          ⟨afterAtomValid, rootMem, oldAtoms, nextIdEq, atomSizeEq⟩
        have allocationSubgraph : Subgraph graph afterAtom := by
          have proof := Graph.Subgraph.allocateAtom (graph := graph)
            (type := type) (label := label)
          rw [allocation] at proof
          exact proof
        have rootOwnerFree : OwnerFree afterAtom root := by
          have proof := valid.allocateAtom_ownerFree (type := type) (label := label)
          rw [allocation] at proof
          exact proof
        have fieldsFree : ∀ name ∈ fields.map Prod.fst,
            FieldFree afterAtom root name := by
          intro name nameMem
          exact rootOwnerFree name
        have fieldsFacts :=
          Graph.addFreshFields_correct afterAtomValid rootMem wellFormed fieldsFree
        rcases fieldsFacts with
          ⟨afterValid, fieldsSubgraph, fieldsEncoded, fieldsSize, fieldsPreserve⟩
        refine ⟨afterValid, allocationSubgraph.trans fieldsSubgraph, ?_, ?_, ?_⟩
        · exact .value (fieldsSubgraph.1 _ rootMem) fieldsEncoded
        · simp only [Node.atomCount]
          omega
        · intro oldOwner name oldHasId oldFree
          have oldFreeAfterAtom := Graph.FieldFree.allocateAtom oldFree
            (type := type) (label := label)
          rw [allocation] at oldFreeAfterAtom
          have oldHasAfterAtom := allocationSubgraph.hasId oldHasId
          have rootEq : root = atomId graph.nextId := by
            have equality := congrArg Prod.fst allocation
            simpa [SpytialLean.Tier1Structural.Graph.allocateAtom, Graph.freshId,
              atomId] using equality.symm
          have oldNeRoot : oldOwner ≠ root := by
            rw [rootEq]
            exact valid.oldId_ne_fresh oldHasId
          exact fieldsPreserve oldOwner name oldHasAfterAtom oldFreeAfterAtom (.inl oldNeRoot)

  theorem Graph.addFreshFields_correct
      {typeKey : Type u} {valueKey : Type v} {graph : Graph}
      {owner ownerType ownerLabel : String}
      {fields : List (String × Node typeKey valueKey)}
      (valid : Valid graph)
      (ownerMem : { id := owner, type := ownerType, label := ownerLabel } ∈ graph.atoms.toList)
      (wellFormed : Node.FieldsWellFormed fields)
      (fieldsFree : ∀ name ∈ fields.map Prod.fst, FieldFree graph owner name) :
      let after := SpytialLean.Tier1Structural.Graph.addFreshFields graph owner ownerType fields
      Valid after ∧ Subgraph graph after ∧ EncodesFields after owner ownerType fields ∧
        after.atoms.size = graph.atoms.size + Node.atomCountFields fields ∧
        (∀ (oldOwner name : String), SpytialLean.Tier1Structural.Graph.HasId graph oldOwner →
          FieldFree graph oldOwner name →
          (oldOwner ≠ owner ∨ name ∉ fields.map Prod.fst) →
          FieldFree after oldOwner name) := by
    cases fields with
    | nil =>
        simp only [SpytialLean.Tier1Structural.Graph.addFreshFields, Node.atomCountFields]
        exact ⟨valid, Graph.Subgraph.refl graph, .nil, rfl,
          fun _ _ _ free _ => free⟩
    | cons field fields =>
        rcases field with ⟨fieldName, child⟩
        change fieldName ∉ fields.map Prod.fst ∧
          Node.WellFormed child ∧ Node.FieldsWellFormed fields at wellFormed
        rcases wellFormed with ⟨fieldNameFresh, childWellFormed, fieldsWellFormed⟩
        have fieldFree := fieldsFree fieldName (by simp)
        have childFacts := Graph.addFreshNode_correct valid childWellFormed
        generalize childRun :
          SpytialLean.Tier1Structural.Graph.addFreshNode graph child = childResult
          at childFacts ⊢
        rcases childResult with ⟨childRoot, afterChild⟩
        rcases childFacts with
          ⟨afterChildValid, childSubgraph, childEncoded, childSize, childPreserve⟩
        have ownerHasId : SpytialLean.Tier1Structural.Graph.HasId graph owner :=
          ⟨{ id := owner, type := ownerType, label := ownerLabel }, ownerMem, rfl⟩
        have ownerMemAfterChild := childSubgraph.1 _ ownerMem
        have fieldFreeAfterChild := childPreserve owner fieldName ownerHasId fieldFree
        let afterField := afterChild.addField fieldName owner ownerType childRoot
          (nodeTypeName child)
        have afterFieldValid : Valid afterField := by
          exact afterChildValid.addField fieldFreeAfterChild ownerMemAfterChild
        have fieldSubgraph : Subgraph afterChild afterField := by
          exact Graph.Subgraph.addField
        have ownerMemAfterField :
            { id := owner, type := ownerType, label := ownerLabel } ∈ afterField.atoms.toList :=
          fieldSubgraph.1 _ ownerMemAfterChild
        have remainingFree : ∀ name ∈ fields.map Prod.fst,
            FieldFree afterField owner name := by
          intro name nameMem
          have before := childPreserve owner name ownerHasId
            (fieldsFree name (by simp [nameMem]))
          apply before.addField_of_name_ne
          intro equality
          apply fieldNameFresh
          simpa [equality] using nameMem
        have remainingFacts := Graph.addFreshFields_correct afterFieldValid ownerMemAfterField
          fieldsWellFormed remainingFree
        rcases remainingFacts with
          ⟨afterValid, remainingSubgraph, remainingEncoded, remainingSize,
            remainingPreserve⟩
        have totalSubgraph : Subgraph graph
            (SpytialLean.Tier1Structural.Graph.addFreshFields afterField owner ownerType fields) :=
          childSubgraph.trans (fieldSubgraph.trans remainingSubgraph)
        have edge := Graph.addField_contains afterChild fieldName owner ownerType childRoot
          (nodeTypeName child)
        rcases edge with ⟨edgeTypes, edgeTuples, edgeFound, edgeMem⟩
        rcases remainingSubgraph.2 fieldName edgeTypes edgeTuples _ edgeFound edgeMem with
          ⟨afterTypes, afterTuples, afterFound, afterMem⟩
        have childEncodedAfter : Encodes
            (SpytialLean.Tier1Structural.Graph.addFreshFields
              afterField owner ownerType fields) childRoot child :=
          childEncoded.mono (fieldSubgraph.trans remainingSubgraph)
        simp only [SpytialLean.Tier1Structural.Graph.addFreshFields, childRun]
        refine ⟨afterValid, totalSubgraph,
          .cons afterFound afterMem childEncodedAfter remainingEncoded, ?_, ?_⟩
        · simp only [Node.atomCountFields]
          change (SpytialLean.Tier1Structural.Graph.addFreshFields
              afterField owner ownerType fields).atoms.size =
            graph.atoms.size + (Node.atomCount child + Node.atomCountFields fields)
          have afterFieldAtoms : afterField.atoms.size = afterChild.atoms.size := by
            simp [afterField, Graph.addField, Graph.addTuple]
          omega
        · intro oldOwner name oldHasId oldFree allowed
          have freeAfterChild := childPreserve oldOwner name oldHasId oldFree
          have oldHasAfterChild := childSubgraph.hasId oldHasId
          have freeAfterField : FieldFree afterField oldOwner name := by
            rcases allowed with ownerDifferent | nameUnused
            · exact freeAfterChild.addField_of_owner_ne ownerDifferent.symm
            · apply freeAfterChild.addField_of_name_ne
              intro equality
              apply nameUnused
              simp [equality]
          have oldHasAfterField := fieldSubgraph.hasId oldHasAfterChild
          apply remainingPreserve oldOwner name oldHasAfterField freeAfterField
          rcases allowed with ownerDifferent | nameUnused
          · exact .inl ownerDifferent
          · exact .inr (fun member => nameUnused (by simp [member]))
end

mutual
  theorem Engine.addNode_asWritten [BEq typeKey] [Hashable typeKey]
      [BEq valueKey] [Hashable valueKey]
      (engine : Engine typeKey valueKey) (node : Node typeKey valueKey) :
      engine.addNode (Node.asWritten node) =
        let (root, graph) := SpytialLean.Tier1Structural.Graph.addFreshNode engine.graph node
        (root, { engine with graph }) := by
    cases node with
    | value identity type label fields =>
        simp only [Node.asWritten, Engine.addNode, Engine.intern, Engine.find?,
          Graph.freshId, Engine.register,
          SpytialLean.Tier1Structural.Graph.addFreshNode,
          SpytialLean.Tier1Structural.Graph.allocateAtom, Graph.addAtom]
        exact congrArg (fun result => (s!"atom_{engine.graph.nextId}", result))
          (Engine.addFields_asWritten
            { engine with
              graph := (engine.graph.freshId.2).addAtom {
                id := s!"atom_{engine.graph.nextId}", type, label } }
            s!"atom_{engine.graph.nextId}" type fields)

  theorem Engine.addFields_asWritten [BEq typeKey] [Hashable typeKey]
      [BEq valueKey] [Hashable valueKey]
      (engine : Engine typeKey valueKey) (owner ownerType : String)
      (fields : List (String × Node typeKey valueKey)) :
      engine.addFields owner ownerType (Node.asWrittenFields fields) =
        { engine with
          graph := SpytialLean.Tier1Structural.Graph.addFreshFields
            engine.graph owner ownerType fields } := by
    cases fields with
    | nil => rfl
    | cons field fields =>
        rcases field with ⟨name, child⟩
        simp only [Node.asWrittenFields, Engine.addFields]
        rw [Engine.addNode_asWritten]
        generalize childRun :
          SpytialLean.Tier1Structural.Graph.addFreshNode engine.graph child = childResult
        rcases childResult with ⟨childRoot, afterChild⟩
        simp only
        rw [Engine.addFields_asWritten]
        simp only [SpytialLean.Tier1Structural.Graph.addFreshFields, childRun]
        cases child <;> rfl
end

theorem relationalize_asWritten_eq [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (node : Node typeKey valueKey) :
    RelationalizerCore.relationalize (Node.asWritten node) =
      let (root, graph) := SpytialLean.Tier1Structural.Graph.addFreshNode ({} : Graph) node
      { root, data := graph.toDataInstance } := by
  unfold RelationalizerCore.relationalize
  rw [Engine.addNode_asWritten]
  rfl

public theorem relationalize_asWritten_represents [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (node : Node typeKey valueKey)
    (wellFormed : Node.WellFormed node) :
    let datum := RelationalizerCore.relationalize (Node.asWritten node)
    Node.representsAt datum.data datum.root (datum.data.atoms.size + 1) node = true := by
  rw [relationalize_asWritten_eq]
  generalize run : SpytialLean.Tier1Structural.Graph.addFreshNode ({} : Graph) node = result
  rcases result with ⟨root, graph⟩
  have facts := Graph.addFreshNode_correct Graph.Valid.empty wellFormed
  rw [run] at facts
  rcases facts with ⟨valid, subgraph, encoded, atomSize, preserves⟩
  apply encoded.representsAt valid
  change Node.depth node ≤ graph.atoms.size + 1
  have depthLe := Node.depth_le_atomCount node
  simp at atomSize
  omega

end SpytialLean.Tier1Structural
