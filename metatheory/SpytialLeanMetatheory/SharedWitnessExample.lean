module

public import SpytialLeanMetatheory.ProofDecoder

public section

/-!
# Shared-witness decoder example

One existential path fact becomes two `edge` tuples that share one semantic
atom. Tuple truth alone would permit independently chosen endpoints; the
explicit `IsTwoEdgePath` result records the identity needed for a connected
diagram.
-/

namespace SpytialLean.Metatheory.SharedWitnessExample

universe u v

public inductive EdgeType where
  | vertex

public inductive EdgeRelation where
  | edge

@[expose] public def signature : RelationalSignature EdgeType where
  Relation := EdgeRelation
  columns
    | .edge => [.vertex, .vertex]

@[expose] public def Carrier (Vertex : Type v) : EdgeType → Type v
  | .vertex => Vertex

@[expose] public def pathContext {World : Type u} {Vertex : Type v}
    (edge : World → Vertex → Vertex → Prop) (source target : Vertex) :
    Iykyk.Metatheory.Context World :=
  fun world => ∃ middle, edge world source middle ∧ edge world middle target

@[expose] public def ground {World : Type u} {Vertex : Type v}
    (edge : World → Vertex → Vertex → Prop) :
    World → GroundInstance signature (Carrier Vertex) :=
  fun world =>
    { holds := fun relation tuple =>
        match relation, tuple with
        | .edge, .cons source (.cons target .nil) => edge world source target }

@[expose] public def constantAtom {World : Type u} {Vertex : Type v}
    {context : Iykyk.Metatheory.Context World} (value : Vertex) :
    ContextualAtom context (Carrier Vertex) .vertex :=
  fun _ _ => value

@[expose] public noncomputable def middleAtom {World : Type u} {Vertex : Type v}
    (edge : World → Vertex → Vertex → Prop) (source target : Vertex) :
    ContextualAtom (pathContext edge source target) (Carrier Vertex) .vertex :=
  fun _ compatible => Classical.choose compatible

@[expose] public def edgeTuple {World : Type u} {Vertex : Type v}
    {context : Iykyk.Metatheory.Context World}
    (source target : ContextualAtom context (Carrier Vertex) .vertex) :
    RelationalTuple signature (ContextualAtom context (Carrier Vertex)) :=
  { relation := .edge
    entries := .cons source (.cons target .nil) }

/-- Two edge tuples form one path only when the endpoint between them is the
    same atom, not merely two values satisfying separate edge facts. -/
public def IsTwoEdgePath {World : Type u} {Vertex : Type v}
    {context : Iykyk.Metatheory.Context World}
    (tuples : List (RelationalTuple signature (ContextualAtom context (Carrier Vertex)))) :
    Prop :=
  ∃ source middle target,
    tuples = [edgeTuple source middle, edgeTuple middle target]

@[expose] public noncomputable def pathTuples {World : Type u} {Vertex : Type v}
    (edge : World → Vertex → Vertex → Prop) (source target : Vertex) :
    List (RelationalTuple signature
      (ContextualAtom (pathContext edge source target) (Carrier Vertex))) :=
  [ edgeTuple (constantAtom source) (middleAtom edge source target),
    edgeTuple (middleAtom edge source target) (constantAtom target) ]

/-- The existential is represented by one atom shared across both tuples. -/
public theorem pathTuples_share_middle {World : Type u} {Vertex : Type v}
    (edge : World → Vertex → Vertex → Prop) (source target : Vertex) :
    IsTwoEdgePath (pathTuples edge source target) := by
  exact ⟨constantAtom source, middleAtom edge source target,
    constantAtom target, rfl⟩

/-- Every compatible world completes both decoded edges, and the middle
    endpoint is definitionally the same contextual atom in both tuples. -/
public theorem decoded_two_edge_path_complete {World : Type u} {Vertex : Type v}
    (edge : World → Vertex → Vertex → Prop) (source target : Vertex) :
    Completes (pathContext edge source target)
      (decodeAtomicFacts (pathContext edge source target) signature (Carrier Vertex)
        (pathTuples edge source target))
      (ground edge) := by
  intro world compatible tuple present
  change tuple ∈ pathTuples edge source target at present
  rw [pathTuples] at present
  cases present with
  | head _ =>
      change edge world source (Classical.choose compatible)
      exact (Classical.choose_spec compatible).1
  | tail _ rest =>
      cases rest with
      | head _ =>
          change edge world (Classical.choose compatible) target
          exact (Classical.choose_spec compatible).2
      | tail _ impossible => contradiction

end SpytialLean.Metatheory.SharedWitnessExample
