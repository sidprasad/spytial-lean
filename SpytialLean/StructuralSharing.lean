module

public import SpytialLean.StructuralEncoding
import all SpytialLean.StructuralEncoding

namespace SpytialLean.StructuralEncoding

open RelationalizerCore

/-!
Structural sharing is safe when each reusable key denotes one constructor/field tree. This
condition concerns the input and its identity policy, not the output datum or the decoder.
The proof below follows the actual `Engine.addNode`/`addFields` computation, including keys
registered before their fields have been visited.
-/

namespace Node

@[expose] public def key? : Node T V → Option (T × V)
  | .value (.keyed type value) _ _ _ => some (type, value)
  | .value .asWritten _ _ _ => none

mutual
  /-- A key denotes the entire exposed structure, with identity annotations erased. -/
  @[expose] public def IdentitySound (meaning : T × V → Node T V) : Node T V → Prop
    | node@(.value _ _ _ fields) =>
        (∀ key, key? node = some key → asWritten node = meaning key) ∧
        FieldsIdentitySound meaning fields

  @[expose] public def FieldsIdentitySound (meaning : T × V → Node T V) :
      List (String × Node T V) → Prop
    | [] => True
    | (_, child) :: fields => IdentitySound meaning child ∧ FieldsIdentitySound meaning fields
end

/-- An occurrence in the finite exposed constructor/field tree, including its root. -/
public inductive Occurs : Node T V → Node T V → Prop where
  | here : Occurs node node
  | field (member : (name, child) ∈ fields) (inside : Occurs node child) :
      Occurs node (.value identity type label fields)

theorem Occurs.trans (inner : Occurs a b) (outer : Occurs b c) : Occurs a c := by
  induction outer with
  | here => exact inner
  | field member inside ih => exact .field member (ih inner)

/-- Structural identity is equality-reflecting across *all* reachable occurrences, including
different instantiated types. It need not merge every pair of equal structures. -/
@[expose] public def Coherent (root : Node T V) : Prop :=
  ∀ a b key, Occurs a root → Occurs b root → key? a = some key → key? b = some key →
    asWritten a = asWritten b

theorem FieldsIdentitySound.member {meaning : T × V → Node T V}
    {fields : List (String × Node T V)} (sound : FieldsIdentitySound meaning fields)
    (member : (name, child) ∈ fields) : IdentitySound meaning child := by
  induction fields with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact sound.1
      · exact ih sound.2 member

theorem IdentitySound.of_occurs {meaning : T × V → Node T V}
    {root node : Node T V} (sound : IdentitySound meaning root) (occurs : Occurs node root) :
    IdentitySound meaning node := by
  revert sound
  induction occurs with
  | here => exact id
  | field member _ ih =>
      intro sound
      exact ih (sound.2.member member)

public theorem IdentitySound.coherent {meaning : T × V → Node T V} {root : Node T V}
    (sound : IdentitySound meaning root) : Coherent root := by
  intro a b key occursA occursB keyA keyB
  cases a
  cases b
  exact ((sound.of_occurs occursA).1 key keyA).trans
    ((sound.of_occurs occursB).1 key keyB).symm

theorem identitySound_of_assignment (root : Node T V) (meaning : T × V → Node T V)
    (assigned : ∀ node, Occurs node root →
      ∀ key, key? node = some key → asWritten node = meaning key) :
    ∀ node, Occurs node root → IdentitySound meaning node := by
  apply Node.rec
    (motive_1 := fun node => Occurs node root → IdentitySound meaning node)
    (motive_2 := fun fields =>
      (∀ name child, (name, child) ∈ fields → Occurs child root) →
        FieldsIdentitySound meaning fields)
    (motive_3 := fun field => Occurs field.2 root → IdentitySound meaning field.2)
  · intro identity type label fields ih occurrence
    refine ⟨assigned _ occurrence, ih ?_⟩
    intro name child member
    exact Occurs.trans (.field member .here) occurrence
  · intro _
    trivial
  · intro head tail headIH tailIH occurrences
    exact ⟨headIH (occurrences head.1 head.2 (by simp)),
      tailIH (fun name child member => occurrences name child (by simp [member]))⟩
  · intro name child ih
    exact ih

/-- The semantic assignment required by the engine theorem follows from the ordinary pairwise
identity law. Choice here is proof-only; it is not an extra encoder or a stored original value. -/
theorem Coherent.exists_meaning {root : Node T V} (coherent : Coherent root) :
    ∃ meaning : T × V → Node T V, IdentitySound meaning root := by
  classical
  let meaning := fun key =>
    if h : ∃ node, Occurs node root ∧ key? node = some key then
      asWritten h.choose
    else asWritten root
  refine ⟨meaning, identitySound_of_assignment root meaning ?_ root .here⟩
  intro node occurrence key found
  have existsNode : ∃ node, Occurs node root ∧ key? node = some key :=
    ⟨node, occurrence, found⟩
  dsimp only [meaning]
  rw [dif_pos existsNode]
  exact coherent node existsNode.choose key occurrence existsNode.choose_spec.1
    found existsNode.choose_spec.2

public theorem coherent_leaf (identity : Identity T V) (type label : String) :
    Coherent (.value identity type label []) := by
  intro a b key occursA occursB _ _
  cases occursA with
  | here =>
      cases occursB with
      | here => rfl
      | field member _ => simp at member
  | field member _ => simp at member

@[expose] public def fields : Node T V → List (String × Node T V)
  | .value _ _ _ children => children

/-- A family closed under immediate fields covers every reachable occurrence. It suffices to
check key compatibility between members of that family, including members of different types.
Automatic losslessness derivation uses the finite family of reachable instantiated field types. -/
public theorem coherent_of_closed (P : Node T V → Prop) (root : Node T V)
    (root_mem : P root)
    (closed : ∀ node, P node → ∀ name child, (name, child) ∈ fields node → P child)
    (compatible : ∀ a b key, P a → P b → key? a = some key → key? b = some key →
      asWritten a = asWritten b) : Coherent root := by
  have covered : ∀ node, Occurs node root → P node := by
    intro node occurs
    induction occurs with
    | here => exact root_mem
    | field member inside ih =>
        exact ih (closed _ root_mem _ _ member)
  intro a b key occursA occursB keyA keyB
  exact compatible a b key (covered a occursA) (covered b occursB) keyA keyB

mutual
  @[simp] theorem depth_asWritten (node : Node T V) : depth (asWritten node) = depth node := by
    cases node with
    | value identity type label fields => simp [asWritten, depth, depthFields_asWritten fields]

  @[simp] theorem depthFields_asWritten (fields : List (String × Node T V)) :
      depthFields (asWrittenFields fields) = depthFields fields := by
    cases fields with
    | nil => rfl
    | cons field fields =>
        rcases field with ⟨name, child⟩
        simp [asWrittenFields, depthFields, depth_asWritten child, depthFields_asWritten fields]
end

end Node

mutual
  theorem Graph.Encodes.asWritten (encoded : Encodes graph root node) :
      Encodes graph root (Node.asWritten node) := by
    cases encoded with
    | value atom fields => exact .value atom fields.asWritten

  theorem Graph.EncodesFields.asWritten {fields : List (String × Node T V)}
      (encoded : EncodesFields graph root type fields) :
      EncodesFields graph root type (Node.asWrittenFields fields) := by
    cases fields with
    | nil => exact .nil
    | cons field fields =>
        rcases field with ⟨name, child⟩
        cases encoded with
        | cons found member childEncoded rest =>
            have childType : nodeTypeName (Node.asWritten child) = nodeTypeName child := by
              cases child <;> rfl
            exact .cons found (by simpa [childType] using member)
              childEncoded.asWritten rest.asWritten
end

mutual
  theorem Graph.Encodes.of_asWritten {node : Node T V}
      (encoded : Encodes graph root (Node.asWritten node)) : Encodes graph root node := by
    cases node with
    | value identity type label fields =>
        cases encoded with
        | value atom fields => exact .value atom fields.of_asWritten

  theorem Graph.EncodesFields.of_asWritten {fields : List (String × Node T V)}
      (encoded : EncodesFields graph root type (Node.asWrittenFields fields)) :
      EncodesFields graph root type fields := by
    cases fields with
    | nil => exact .nil
    | cons field fields =>
        rcases field with ⟨name, child⟩
        cases encoded with
        | cons found member childEncoded rest =>
            have childType : nodeTypeName (Node.asWritten child) = nodeTypeName child := by
              cases child <;> rfl
            exact .cons found (by simpa [childType] using member)
              childEncoded.of_asWritten rest.of_asWritten
end

namespace Sharing

variable {T : Type u} {V : Type v} [BEq T] [Hashable T] [BEq V] [Hashable V]
  [LawfulBEq T] [LawfulBEq V]

/-- Ancestors reserve one atom each. Only keyed ancestors can appear in the reuse table. -/
abbrev Pending (T : Type u) (V : Type v) := List (Option (T × V) × String)

def CacheValid (meaning : T × V → Node T V) (pending : Pending T V)
    (engine : Engine T V) : Prop :=
  ∀ key root, engine.identities[key]? = some root →
    (Graph.Encodes engine.graph root (meaning key) ∧
      Node.depth (meaning key) ≤ engine.graph.atoms.size - pending.length) ∨
    (some key, root) ∈ pending

def BelowPending (meaning : T × V → Node T V) (pending : Pending T V) (depth : Nat) :=
  ∀ key root, (some key, root) ∈ pending → depth < Node.depth (meaning key)

def beginNode (engine : Engine T V) (identity : Identity T V) (type label : String) :
    Engine T V :=
  { engine.register identity (atomId engine.graph.nextId) with
    graph := (Graph.allocateAtom engine.graph type label).2 }

omit [LawfulBEq T] [LawfulBEq V] in
theorem addNode_fresh (engine : Engine T V) (identity : Identity T V)
    (type label : String) (fields : List (String × Node T V))
    (fresh : engine.find? identity = none) :
    engine.addNode (.value identity type label fields) =
      (atomId engine.graph.nextId,
        (beginNode engine identity type label).addFields
          (atomId engine.graph.nextId) type fields) := by
  simp only [Engine.addNode, Engine.intern, fresh]
  cases identity <;> rfl

omit [LawfulBEq T] [LawfulBEq V] in
theorem cache_mono {meaning : T × V → Node T V} {pending : Pending T V}
    {before after : Engine T V} (cache : CacheValid meaning pending before)
    (identities : after.identities = before.identities)
    (subgraph : Graph.Subgraph before.graph after.graph)
    (size : before.graph.atoms.size ≤ after.graph.atoms.size) :
    CacheValid meaning pending after := by
  intro key root found
  rw [identities] at found
  rcases cache key root found with ⟨encoded, bound⟩ | ancestor
  · exact .inl ⟨encoded.mono subgraph, by omega⟩
  · exact .inr ancestor

theorem cache_begin {meaning : T × V → Node T V} {pending : Pending T V}
    {engine : Engine T V} {identity : Identity T V} {type label : String}
    {fields : List (String × Node T V)} (cache : CacheValid meaning pending engine) :
    CacheValid meaning
      ((Node.key? (.value identity type label fields), atomId engine.graph.nextId) :: pending)
      (beginNode engine identity type label) := by
  intro key root found
  have subgraph := Graph.Subgraph.allocateAtom
    (graph := engine.graph) (type := type) (label := label)
  have old : engine.identities[key]? = some root →
      (Graph.Encodes (beginNode engine identity type label).graph root (meaning key) ∧
        Node.depth (meaning key) ≤
          (beginNode engine identity type label).graph.atoms.size - (pending.length + 1)) ∨
      (some key, root) ∈ pending := by
    intro found
    rcases cache key root found with ⟨encoded, bound⟩ | ancestor
    · refine .inl ⟨encoded.mono subgraph, ?_⟩
      simpa [beginNode, Graph.allocateAtom, Graph.addAtom, Graph.freshId] using bound
    · exact .inr ancestor
  cases identity with
  | asWritten =>
      change engine.identities[key]? = some root at found
      rcases old found with completed | ancestor
      · exact .inl completed
      · exact .inr (List.mem_cons_of_mem _ ancestor)
  | keyed type value =>
      change (engine.identities.insert (type, value) (atomId engine.graph.nextId))[key]? =
        some root at found
      rw [Std.HashMap.getElem?_insert] at found
      split at found
      next same =>
        have keyEq : (type, value) = key := by simpa using same
        have rootEq : atomId engine.graph.nextId = root := Option.some.inj found
        exact .inr (by simp [Node.key?, keyEq, rootEq])
      next different =>
        rcases old found with completed | ancestor
        · exact .inl completed
        · exact .inr (List.mem_cons_of_mem _ ancestor)

-- The mutual proof shares the map-equality assumptions even though only the node case
-- directly invokes a HashMap insertion lemma.
set_option linter.unusedSectionVars false in
mutual
  theorem addNode_correct {meaning : T × V → Node T V} {pending : Pending T V}
      {engine : Engine T V} {node : Node T V}
      (valid : Graph.Valid engine.graph) (cache : CacheValid meaning pending engine)
      (reserved : pending.length ≤ engine.graph.atoms.size)
      (below : BelowPending meaning pending (Node.depth node))
      (wellFormed : Node.WellFormed node) (sound : Node.IdentitySound meaning node) :
      let (root, after) := engine.addNode node
      Graph.Valid after.graph ∧ Graph.Subgraph engine.graph after.graph ∧
        CacheValid meaning pending after ∧ Graph.Encodes after.graph root node ∧
        Node.depth node ≤ after.graph.atoms.size - pending.length ∧
        engine.graph.atoms.size ≤ after.graph.atoms.size ∧
        Graph.PreservesOldFieldFree engine.graph after.graph := by
    cases node with
    | value identity type label fields =>
        cases found : engine.find? identity with
        | some root =>
            cases identity with
            | asWritten => simp [Engine.find?] at found
            | keyed keyType keyValue =>
                have denotes := sound.1 (keyType, keyValue) rfl
                have depthEq : Node.depth (meaning (keyType, keyValue)) =
                    Node.depth (.value (.keyed keyType keyValue) type label fields) := by
                  rw [← denotes, Node.depth_asWritten]
                rcases cache (keyType, keyValue) root found with ⟨encoded, bound⟩ | ancestor
                · simp only [Engine.addNode, Engine.intern, found]
                  refine ⟨valid, Graph.Subgraph.refl _, cache, ?_, ?_, Nat.le_refl _, ?_⟩
                  · apply Graph.Encodes.of_asWritten
                    simpa [denotes] using encoded
                  · simpa [depthEq] using bound
                  · exact fun _ _ _ free => free
                · have smaller := below _ _ ancestor
                  omega
        | none =>
            rw [addNode_fresh engine identity type label fields found]
            let root := atomId engine.graph.nextId
            let start := beginNode engine identity type label
            let stack := (Node.key? (.value identity type label fields), root) :: pending
            have allocation := valid.allocateAtom (type := type) (label := label)
            have startValid : Graph.Valid start.graph := allocation.1
            have rootMem : { id := root, type, label } ∈ start.graph.atoms.toList :=
              allocation.2.1
            have sizeStart : start.graph.atoms.size = engine.graph.atoms.size + 1 :=
              allocation.2.2.2.2
            have subgraphStart : Graph.Subgraph engine.graph start.graph :=
              Graph.Subgraph.allocateAtom
            have cacheStart : CacheValid meaning stack start := cache_begin cache
            have fieldsFree : ∀ name ∈ fields.map Prod.fst,
                Graph.FieldFree start.graph root (fieldRelationId type name) := by
              intro name _
              exact valid.allocateAtom_ownerFree (fieldRelationId type name)
            have belowFields : BelowPending meaning stack (Node.depthFields fields) := by
              intro key id ancestor
              rcases List.mem_cons.mp ancestor with same | ancestor
              · have keyEq : Node.key? (.value identity type label fields) = some key :=
                  (congrArg Prod.fst same).symm
                have denotes := sound.1 key keyEq
                have depths := congrArg Node.depth denotes
                simp only [Node.depth_asWritten, Node.depth] at depths
                omega
              · have deeper := below key id ancestor
                simp only [Node.depth] at deeper
                omega
            have reservedStart : stack.length ≤ start.graph.atoms.size := by
              simp only [stack, List.length_cons]
              omega
            have facts := addFields_correct startValid cacheStart reservedStart belowFields
              rootMem wellFormed sound.2 fieldsFree
            rcases facts with
              ⟨afterValid, subgraphFields, cacheFields, encodedFields, depthFields,
                sizeFields, preserveFields⟩
            let after := start.addFields root type fields
            dsimp only [after, root, start, stack] at *
            have encoded : Graph.Encodes after.graph root (.value identity type label fields) :=
              .value (subgraphFields.1 _ rootMem) encodedFields
            have depthBound : Node.depth (.value identity type label fields) ≤
                after.graph.atoms.size - pending.length := by
              dsimp only [after, root, start]
              change Node.depthFields fields + 1 ≤ _
              simp only [List.length_cons] at depthFields reservedStart
              omega
            refine ⟨afterValid, subgraphStart.trans subgraphFields, ?_, encoded,
              depthBound, by omega, ?_⟩
            · intro key id lookup
              rcases cacheFields key id lookup with ⟨oldEncoded, oldBound⟩ | ancestor
              · refine .inl ⟨oldEncoded, ?_⟩
                simp only [List.length_cons] at oldBound
                omega
              · rcases List.mem_cons.mp ancestor with same | ancestor
                · have keyEq : Node.key? (.value identity type label fields) = some key :=
                    (congrArg Prod.fst same).symm
                  have rootEq : id = root := congrArg Prod.snd same
                  have denotes := sound.1 key keyEq
                  refine .inl ⟨?_, ?_⟩
                  · rw [rootEq, ← denotes]
                    exact encoded.asWritten
                  · rw [← denotes, Node.depth_asWritten]
                    exact depthBound
                · exact .inr ancestor
            · intro oldOwner name oldHasId oldFree
              have oldFreeStart : Graph.FieldFree start.graph oldOwner name :=
                oldFree.allocateAtom
              apply preserveFields oldOwner name (subgraphStart.hasId oldHasId) oldFreeStart
              exact .inl (valid.oldId_ne_fresh oldHasId)
  termination_by Node.count node
  decreasing_by all_goals subst_vars; simp only [Node.count]; omega

  theorem addFields_correct {meaning : T × V → Node T V} {pending : Pending T V}
      {engine : Engine T V} {owner ownerType ownerLabel : String}
      {fields : List (String × Node T V)}
      (valid : Graph.Valid engine.graph) (cache : CacheValid meaning pending engine)
      (reserved : pending.length ≤ engine.graph.atoms.size)
      (below : BelowPending meaning pending (Node.depthFields fields))
      (ownerMem : { id := owner, type := ownerType, label := ownerLabel } ∈
        engine.graph.atoms.toList)
      (wellFormed : Node.FieldsWellFormed fields)
      (sound : Node.FieldsIdentitySound meaning fields)
      (fieldsFree : ∀ name ∈ fields.map Prod.fst,
        Graph.FieldFree engine.graph owner (fieldRelationId ownerType name)) :
      let after := engine.addFields owner ownerType fields
      Graph.Valid after.graph ∧ Graph.Subgraph engine.graph after.graph ∧
        CacheValid meaning pending after ∧ Graph.EncodesFields after.graph owner ownerType fields ∧
        Node.depthFields fields ≤ after.graph.atoms.size - pending.length ∧
        engine.graph.atoms.size ≤ after.graph.atoms.size ∧
        (∀ oldOwner name, Graph.HasId engine.graph oldOwner →
          Graph.FieldFree engine.graph oldOwner name →
          (oldOwner ≠ owner ∨ name ∉ fields.map (fun f => fieldRelationId ownerType f.1)) →
          Graph.FieldFree after.graph oldOwner name) := by
    cases fields with
    | nil =>
        simp only [Engine.addFields_nil]
        exact ⟨valid, Graph.Subgraph.refl _, cache, .nil, Nat.zero_le _, Nat.le_refl _,
          fun _ _ _ free _ => free⟩
    | cons field fields =>
        let fieldName := field.1
        let child := field.2
        rcases wellFormed with ⟨fieldNameFresh, childWellFormed, fieldsWellFormed⟩
        have belowChild : BelowPending meaning pending (Node.depth child) := by
          intro key id member
          have bound := below key id member
          change max (Node.depth child) (Node.depthFields fields) < _ at bound
          omega
        have belowRest : BelowPending meaning pending (Node.depthFields fields) := by
          intro key id member
          have bound := below key id member
          change max (Node.depth child) (Node.depthFields fields) < _ at bound
          omega
        have childFacts := addNode_correct valid cache reserved belowChild childWellFormed sound.1
        generalize childRun : engine.addNode child = childResult at childFacts
        rcases childResult with ⟨childRoot, afterChild⟩
        rcases childFacts with
          ⟨childValid, childSubgraph, childCache, childEncoded, childDepth,
            childSize, childPreserve⟩
        have ownerHasId : Graph.HasId engine.graph owner :=
          ⟨{ id := owner, type := ownerType, label := ownerLabel }, ownerMem, rfl⟩
        have ownerAfterChild := childSubgraph.1 _ ownerMem
        have fieldFree := childPreserve owner (fieldRelationId ownerType fieldName) ownerHasId
          (fieldsFree fieldName (by simp [fieldName]))
        let afterField : Engine T V := { afterChild with
          graph := afterChild.graph.addField fieldName owner ownerType childRoot
            (nodeTypeName child) }
        have fieldValid : Graph.Valid afterField.graph :=
          childValid.addField fieldFree ownerAfterChild
        have fieldSubgraph : Graph.Subgraph afterChild.graph afterField.graph :=
          Graph.Subgraph.addField
        have fieldSize : afterField.graph.atoms.size = afterChild.graph.atoms.size := rfl
        have fieldCache : CacheValid meaning pending afterField :=
          cache_mono childCache rfl fieldSubgraph (by omega)
        have reservedField : pending.length ≤ afterField.graph.atoms.size := by omega
        have remainingFree : ∀ name ∈ fields.map Prod.fst,
            Graph.FieldFree afterField.graph owner (fieldRelationId ownerType name) := by
          intro name nameMem
          have before := childPreserve owner (fieldRelationId ownerType name) ownerHasId
            (fieldsFree name (by simp [nameMem]))
          apply before.addField_of_id_ne
          intro equality
          have equality := fieldRelationId_injective ownerType equality
          exact fieldNameFresh (by simpa [← equality, fieldName] using nameMem)
        have remainingFacts := addFields_correct fieldValid fieldCache reservedField belowRest
          (fieldSubgraph.1 _ ownerAfterChild) fieldsWellFormed sound.2 remainingFree
        rcases remainingFacts with
          ⟨afterValid, restSubgraph, afterCache, restEncoded, restDepth, restSize, restPreserve⟩
        have edge := Graph.addField_contains afterChild.graph fieldName owner ownerType childRoot
          (nodeTypeName child)
        rcases edge with ⟨edgeRelation, edgeFound, edgeMem⟩
        rcases restSubgraph.2 _ edgeRelation _ edgeFound edgeMem with
          ⟨afterRelation, afterFound, afterMem⟩
        rw [Engine.addFields_cons, childRun]
        refine ⟨afterValid, childSubgraph.trans (fieldSubgraph.trans restSubgraph), afterCache,
          .cons afterFound afterMem (childEncoded.mono (fieldSubgraph.trans restSubgraph))
            restEncoded, ?_, ?_, ?_⟩
        · change max (Node.depth child) (Node.depthFields fields) ≤
            (afterField.addFields owner ownerType fields).graph.atoms.size - pending.length
          omega
        · change engine.graph.atoms.size ≤
            (afterField.addFields owner ownerType fields).graph.atoms.size
          omega
        · intro oldOwner name oldHasId oldFree allowed
          have freeChild := childPreserve oldOwner name oldHasId oldFree
          have freeField : Graph.FieldFree afterField.graph oldOwner name := by
            rcases allowed with different | unused
            · exact freeChild.addField_of_owner_ne different.symm
            · apply freeChild.addField_of_id_ne
              intro equality
              exact unused (by simp [← equality, fieldName])
          apply restPreserve oldOwner name
            (fieldSubgraph.hasId (childSubgraph.hasId oldHasId)) freeField
          rcases allowed with different | unused
          · exact .inl different
          · exact .inr (fun member => unused (by simp [member]))
  termination_by Node.countFields fields
  decreasing_by
    all_goals subst_vars; simp only [Node.countFields]
    all_goals omega
end

end Sharing

/-- Universal preservation by the actual identity-aware engine. The hypothesis describes only
what keys mean on the input structure; it does not assume successful decoding or run a check. -/
public theorem walk_sharing_represents [BEq T] [Hashable T] [BEq V] [Hashable V]
    [LawfulBEq T] [LawfulBEq V] (node : Node T V) (meaning : T × V → Node T V)
    (wellFormed : Node.WellFormed node) (sound : Node.IdentitySound meaning node) :
    let datum := RelationalizerCore.walk node
    Node.representsAt datum.data datum.root (datum.data.atoms.size + 1) node = true := by
  have cache : Sharing.CacheValid meaning [] (Engine.empty : Engine T V) := by
    intro key root found
    simp [Engine.empty] at found
  have below : Sharing.BelowPending meaning [] (Node.depth node) := by
    intro key root member
    simp at member
  have facts := Sharing.addNode_correct Graph.Valid.empty cache (by simp [Engine.empty])
    below wellFormed sound
  unfold RelationalizerCore.walk
  generalize run : (Engine.empty : Engine T V).addNode node = result at facts ⊢
  rcases result with ⟨root, after⟩
  rcases facts with ⟨valid, _, _, encoded, depth, _, _⟩
  apply encoded.representsAt valid
  simp only [List.length_nil, Nat.sub_zero] at depth
  exact Nat.le_trans depth (Nat.le_succ _)

/-- Pairwise equality-reflection of reuse keys suffices for reconstruction after sharing. -/
public theorem walk_coherent_represents [BEq T] [Hashable T] [BEq V] [Hashable V]
    [LawfulBEq T] [LawfulBEq V] (node : Node T V)
    (wellFormed : Node.WellFormed node) (coherent : Node.Coherent node) :
    let datum := RelationalizerCore.walk node
    Node.representsAt datum.data datum.root (datum.data.atoms.size + 1) node = true := by
  obtain ⟨meaning, sound⟩ := coherent.exists_meaning
  exact walk_sharing_represents node meaning wellFormed sound

end SpytialLean.StructuralEncoding
