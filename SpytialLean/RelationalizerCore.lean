module

public import SpytialLean.Types

namespace SpytialLean.RelationalizerCore

/-!
# Pure relational data construction

This module is the environment-independent part of relationalization. It owns atom allocation,
relation accumulation, and conversion to `JsonDataInstance`. It does not inspect `Lean.Expr`,
evaluate values, choose an identity policy, or retain selector evidence; those are responsibilities
of the `MetaM` adapter in `Relationalizer`.

Keeping these transitions pure gives a typed Tier 1 frontend one engine to target. It must use this
state rather than implement a second path from values to relational data.
-/

/-- The graph state shared by relationalization frontends. -/
public structure Graph where
  atoms : Array JsonAtom := #[]
  /-- Map from relation name to its declared column types and accumulated tuples. -/
  relations : Std.HashMap String (Array String × Array JsonTuple) := {}
  nextId : Nat := 0

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

end SpytialLean.RelationalizerCore
