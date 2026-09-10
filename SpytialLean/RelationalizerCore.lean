module

public import SpytialLean.Types

namespace SpytialLean.RelationalizerCore

/-!
# Shared relationalization engine

This is the environment-independent graph-building state machine. It owns atom allocation,
identity interning, relation accumulation, and conversion to `JsonDataInstance`.

`walk` traverses an already-exposed structural `Node`. The expression adapter instead drives the
same `Engine` and `Graph` transitions incrementally while it discovers `Lean.Expr` structure, since
it must also retain expression provenance and selector evidence. Typed Tier 1 exposure materializes
the structural node through generated pattern matching and calls `walk`. Neither adapter owns a
second graph builder.
-/

/-- The graph state shared by relationalization frontends. -/
public structure Graph where
  atoms : Array JsonAtom := #[]
  /-- Map from relation name to its declared column types and accumulated tuples. -/
  relations : Std.HashMap String (Array String × Array JsonTuple) := {}
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
    (tuple : JsonTuple) : Graph :=
  let existing := graph.relations.getD name (types, #[])
  { graph with relations := graph.relations.insert name (existing.1, existing.2.push tuple) }

/-- Add the binary relation edge used for an ordinary constructor or structure field. -/
@[expose] public def Graph.addField (graph : Graph)
    (name owner ownerType child childType : String) : Graph :=
  let types := #[ownerType, childType]
  graph.addTuple name types { atoms := #[owner, child], types }

/-- Register a relation with no tuples, preserving an empty extension in the resulting datum. -/
@[expose] public def Graph.addRelation (graph : Graph)
    (name : String) (types : Array String) : Graph :=
  if graph.relations.contains name then graph
  else { graph with relations := graph.relations.insert name (types, #[]) }

/-- Materialize the ordinary relational datum represented by the graph state. -/
@[expose] public def Graph.toDataInstance (graph : Graph) : JsonDataInstance :=
  let relations := graph.relations.toArray.map fun (name, types, tuples) =>
    { id := name, name, types, tuples : JsonRelation }
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
            let graph := engine.graph.addAtom { id, type, label }
            let engine := { engine with graph }
            (id, engine.addFields id type fields)

  /-- Relationalize a node's fields from left to right. -/
  @[expose] public def Engine.addFields [BEq typeKey] [Hashable typeKey]
      [BEq valueKey] [Hashable valueKey] (engine : Engine typeKey valueKey)
      (owner ownerType : String) :
      List (String × Node typeKey valueKey) → Engine typeKey valueKey
    | [] => engine
    | (name, child) :: fields =>
        let (childId, engine) := engine.addNode child
        let childType := match child with | .value _ type _ _ => type
        let graph := engine.graph.addField name owner ownerType childId childType
        { engine with graph }.addFields owner ownerType fields
end

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
