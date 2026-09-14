module

public import SpytialLean.Types

namespace SpytialLean.RelationalizerCore

/-!
# Shared relationalization engine

This is the environment-independent graph-building state machine. It owns atom allocation,
identity interning, relation accumulation, and conversion to `JsonDataInstance`.

`emitStructure` and `visitFields` own ordinary node emission and left-to-right field traversal.
They run in a pure state monad for an already-exposed `Node`, or in the expression adapter's
`MetaM` state while it discovers structure and retains provenance and selector evidence. The
adapters supply field exposure, child inspection, and graph-state access; neither implements a
second constructor-field traversal. Identity and non-structural expression handling are unchanged.
-/

/-- Stored relation metadata; its ID is the graph map's key. -/
public structure RelationData where
  name : String
  types : Array String
  tuples : Array JsonTuple

/-- The graph state shared by relationalization frontends. -/
public structure Graph where
  atoms : Array JsonAtom := #[]
  /-- Relations indexed by identity, independently of their selector names. -/
  relations : Std.HashMap String RelationData := {}
  nextId : Nat := 0

/-- An identity request supplied by a frontend after it has chosen the policy and computed keys. -/
public inductive Identity (typeKey : Type u) (valueKey : Type v) where
  /-- Allocate a distinct atom for this occurrence. -/
  | asWritten
  /-- Reuse the atom with this type-and-value key, if one has already been allocated. -/
  | keyed (type : typeKey) (value : valueKey)

/-- Whether identity resolution allocated an atom or reused an existing one. -/
public inductive Allocation where
  | fresh (id : String)
  | reused (id : String)
  deriving Repr, BEq, DecidableEq

/-- A frontend-neutral structural value presented to the relationalization engine. -/
public inductive Node (typeKey : Type u) (valueKey : Type v) where
  | value
      (identity : Identity typeKey valueKey)
      (type label : String)
      (fields : List (String × Node typeKey valueKey))

/-- Traverse ordinary fields in source order. Exposure may skip a field (a proof, or a function
already tabulated by the expression adapter). Otherwise visit the child before inspecting its
column type and emitting its edge. Keeping this order preserves expression-adapter effects. -/
@[expose] public def visitFields {m : Type u → Type v} [Monad m] {field child : Type u}
    (prepare : field → m (Option (String × child))) (recurse : child → m (ULift.{u} String))
    (childType : child → m (ULift.{u} String))
    (addField : String → String → String → String → String → m PUnit)
    (owner ownerType : String) (fields : List field) : m PUnit :=
  fields.forM fun field => do
    if let some (name, child) ← prepare field then
      let childId ← recurse child
      let type ← childType child
      addField name owner ownerType childId.down type.down

/-- Emit a fresh structural atom before visiting its fields. Allocation and reuse happen before
this operation, so reusing an atom never exposes or traverses its children. -/
@[expose] public def emitStructure {m : Type u → Type v} [Monad m]
    (addAtom : JsonAtom → m PUnit) (atom : JsonAtom) (fields : m PUnit) : m PUnit := do
  addAtom atom
  fields

/-- The identity-aware state shared by structural relationalization frontends. -/
public structure Engine (typeKey : Type u) (valueKey : Type v)
    [BEq typeKey] [Hashable typeKey] [BEq valueKey] [Hashable valueKey] where
  graph : Graph
  identities : Std.HashMap (typeKey × valueKey) String

/-- An empty identity-aware relationalization engine. -/
@[expose] public def Engine.empty [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] :
    Engine typeKey valueKey :=
  { graph := {}, identities := {} }

/-- Generate the next atom ID and advance the allocator. -/
@[expose] public def Graph.freshId (graph : Graph) : String × Graph :=
  let id := s!"atom_{graph.nextId}"
  (id, { graph with nextId := graph.nextId + 1 })

/-- Append one atom to the graph. -/
@[expose] public def Graph.addAtom (graph : Graph) (atom : JsonAtom) : Graph :=
  { graph with atoms := graph.atoms.push atom }

/-- Add a tuple, creating its named relation when this is the first tuple. -/
@[expose] public def Graph.addTuple (graph : Graph) (name : String) (types : Array String)
    (tuple : JsonTuple) (id : String := name) : Graph :=
  let existing := graph.relations.getD id { name, types, tuples := #[] }
  let updated := { existing with tuples := existing.tuples.push tuple }
  { graph with relations := graph.relations.insert id updated }

/-- Add the binary relation edge used for an ordinary constructor or structure field. -/
@[expose] public def Graph.addField (graph : Graph)
    (name owner ownerType child childType : String) : Graph :=
  let types := #[ownerType, childType]
  graph.addTuple name types { atoms := #[owner, child], types } (fieldRelationId ownerType name)

/-- Register a relation with no tuples, preserving an empty extension in the resulting datum. -/
@[expose] public def Graph.addRelation (graph : Graph)
    (name : String) (types : Array String) (id : String := name) : Graph :=
  if graph.relations.contains id then graph
  else { graph with relations := graph.relations.insert id { name, types, tuples := #[] } }

/-- Materialize the ordinary relational datum represented by the graph state. -/
@[expose] public def Graph.toDataInstance (graph : Graph) : JsonDataInstance :=
  let relations := graph.relations.toArray.map fun (id, relation) =>
    { id, name := relation.name, types := relation.types, tuples := relation.tuples : JsonRelation }
  { atoms := graph.atoms, relations }

/-- Look up the atom selected by an identity request. `asWritten` never selects one. -/
@[expose] public def Engine.find? [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey) :
    Identity typeKey valueKey → Option String
  | .asWritten => none
  | .keyed type value => engine.identities[(type, value)]?

/-- Register a freshly allocated atom under a structural identity request. -/
@[expose] public def Engine.register [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey)
    (identity : Identity typeKey valueKey) (id : String) : Engine typeKey valueKey :=
  match identity with
  | .asWritten => engine
  | .keyed type value =>
      { engine with identities := engine.identities.insert (type, value) id }

/-- Registering an identity never changes the relational graph. -/
@[simp] public theorem Engine.register_graph [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey)
    (identity : Identity typeKey valueKey) (id : String) :
    (engine.register identity id).graph = engine.graph := by
  cases identity <;> rfl

/-- Resolve identity and allocate exactly when this is a new occurrence. -/
@[expose] public def Engine.intern [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey)
    (identity : Identity typeKey valueKey) : Allocation × Engine typeKey valueKey :=
  match engine.find? identity with
  | some id => (.reused id, engine)
  | none =>
      let (id, graph) := engine.graph.freshId
      let engine := { engine with graph }
      (.fresh id, engine.register identity id)

mutual
  /-- Relationalize one structural node, reusing or allocating its atom according to identity. -/
  @[expose] public def Engine.addNode [BEq typeKey] [Hashable typeKey]
      [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey) :
      Node typeKey valueKey → String × Engine typeKey valueKey
    | .value identity type label fields =>
        match engine.intern identity with
        | (.reused id, engine) => (id, engine)
        | (.fresh id, engine) =>
            let (_, engine) := (emitStructure
              (m := StateM (Engine typeKey valueKey))
              (fun atom => modify fun state => { state with graph := state.graph.addAtom atom })
              { id, type, label }
              (modify fun state => state.addFields id type fields)).run engine
            (id, engine)
  termination_by node => sizeOf node

  /-- Relationalize a node's fields from left to right. -/
  @[expose] public def Engine.addFields [BEq typeKey] [Hashable typeKey]
      [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey)
      (owner ownerType : String) (fields : List (String × Node typeKey valueKey)) :
      Engine typeKey valueKey :=
    (visitFields (m := StateM (Engine typeKey valueKey))
      (fun field => pure (some (field.val.1, field)))
      (fun field => modifyGet fun state =>
        let (id, state) := state.addNode field.val.2
        (ULift.up id, state))
      (fun field => pure ⟨match field.val.2 with | .value _ type _ _ => type⟩)
      (fun name owner ownerType child childType =>
        modify fun state =>
          { state with graph := state.graph.addField name owner ownerType child childType })
      owner ownerType fields.attach).run engine |>.2
  termination_by sizeOf fields
  decreasing_by
    have smaller := List.sizeOf_lt_of_mem field.property
    simp_wf
    have : sizeOf field.val.2 < sizeOf field.val := by
      cases field.val
      simp +arith
    omega
end

/-- The membership witnesses used to justify recursive child visits have no runtime effect. -/
public theorem Engine.addFields_eq [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey)
    (owner ownerType : String) (fields : List (String × Node typeKey valueKey)) :
    engine.addFields owner ownerType fields =
      ((fields.forM fun (name, child) => do
        let childType := match child with | .value _ type _ _ => type
        modify fun state =>
          let (childId, state) := state.addNode child
          { state with graph := state.graph.addField name owner ownerType childId childType }
        : StateM (Engine typeKey valueKey) PUnit).run engine).2 := by
  simp only [Engine.addFields, visitFields, pure_bind]
  let step : (String × Node typeKey valueKey) → StateM (Engine typeKey valueKey) PUnit :=
    fun (name, child) => modify fun state =>
      let (childId, state) := state.addNode child
      let childType := match child with | .value _ type _ _ => type
      { state with graph := state.graph.addField name owner ownerType childId childType }
  have mapped := List.forM_map (l := fields.attach) (g := Subtype.val) (f := step)
  rw [List.attach_map_subtype_val] at mapped
  exact congrArg (fun action => (action.run engine).2) mapped.symm

@[simp] public theorem Engine.addFields_nil [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey)
    (owner ownerType : String) : engine.addFields owner ownerType [] = engine := by
  rw [Engine.addFields_eq]
  rfl

public theorem Engine.addFields_cons [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey)
    (owner ownerType name : String) (child : Node typeKey valueKey)
    (fields : List (String × Node typeKey valueKey)) :
    engine.addFields owner ownerType ((name, child) :: fields) =
      let (childId, engine) := engine.addNode child
      let childType := match child with | .value _ type _ _ => type
      { engine with graph := engine.graph.addField name owner ownerType childId childType
        }.addFields owner ownerType fields := by
  simp only [Engine.addFields_eq]
  rfl

/-- Walk one distinguished structural node with the shared identity-aware engine. -/
@[expose] public def walk [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey]
    (node : Node typeKey valueKey) : RootedJsonDataInstance :=
  let (root, engine) := (Engine.empty : Engine typeKey valueKey).addNode node
  { root, data := engine.graph.toDataInstance }

/-- Compatibility name for callers of the original extracted graph core. -/
@[expose] public def relationalize [BEq typeKey] [Hashable typeKey]
    [BEq valueKey] [Hashable valueKey]
    (node : Node typeKey valueKey) : RootedJsonDataInstance :=
  walk node

end SpytialLean.RelationalizerCore
