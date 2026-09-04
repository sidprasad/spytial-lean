module

public import Lean

namespace SpytialLean

open Lean

/-- A single atom in the relational data instance consumed by Spytial. -/
public structure JsonAtom where
  id : String
  type : String
  label : String
  deriving ToJson, FromJson, Inhabited

/-- A tuple in a relation: an ordered list of atom IDs with their types. -/
public structure JsonTuple where
  atoms : Array String
  types : Array String
  deriving ToJson, FromJson, Inhabited

/-- A named relation and its known tuples. -/
public structure JsonRelation where
  id : String
  name : String
  types : Array String
  tuples : Array JsonTuple
  deriving ToJson, FromJson, Inhabited

/-- The relational data instance passed to Spytial's rendering pipeline. -/
public structure JsonDataInstance where
  atoms : Array JsonAtom
  relations : Array JsonRelation
  deriving ToJson, FromJson, Inhabited

/-- Why the production relationalizer emitted one tuple. The core semantics
    interprets `structural` and `proved`. All other built-in features remain
    visible as `other` without acquiring semantic obligations here. -/
public inductive TupleOrigin where
  /-- Constructor fields and structure projections. -/
  | structural (terms : Array Expr)
  /-- A proposition/proof pair obtained from IYKYK knowledge. -/
  | proved (proposition proof : Expr) (terms : Array Expr)
  /-- A built-in origin outside the first theorem, such as an observation,
      tabulation row, symbolic graph, or synthetic display edge. -/
  | other
  /-- Output supplied by an unrestricted custom relationalizer. -/
  | custom
  deriving Inhabited

/-- One tuple together with its production origin. More than one entry may
    justify the same tuple. -/
public structure TupleEmission where
  relation : String
  tuple : JsonTuple
  origin : TupleOrigin
  deriving Inhabited

/-- The relational instance before production evidence is erased for JSON. -/
public structure TracedDataInstance where
  data : JsonDataInstance
  emissions : Array TupleEmission
  deriving Inhabited

/-- A tuple has exactly one type for each atom occurrence. -/
public def JsonTuple.columnsAligned (tuple : JsonTuple) : Bool :=
  tuple.atoms.size == tuple.types.size

/-- Every tuple has aligned columns and refers only to output atoms. Type
    strings are not compared: declared aliases may differ from reduced atom
    types even when the underlying Lean types are definitionally equal. -/
public def JsonDataInstance.tuplesWellFormed (data : JsonDataInstance) : Bool :=
  data.relations.all fun relation =>
    relation.tuples.all fun tuple =>
      tuple.columnsAligned && (tuple.atoms.zip tuple.types).all fun (id, _) =>
        data.atoms.any fun atom => atom.id == id

/-- The Lean terms claimed for the tuple's columns, when the origin kind has
    such an interpretation. -/
public def TupleOrigin.terms? : TupleOrigin → Option (Array Expr)
  | .structural terms
  | .proved _ _ terms => some terms
  | .other
  | .custom => none

/-- Does an emission describe this exact output tuple? -/
@[expose] public def TupleEmission.matches (emission : TupleEmission)
    (relation : JsonRelation) (tuple : JsonTuple) : Bool :=
  emission.relation == relation.name && emission.tuple.atoms == tuple.atoms &&
    emission.tuple.types == tuple.types

/-- Every interpreted column has one Lean term. Custom output makes no generic
    term-interpretation claim. -/
public def TupleEmission.termsAligned (emission : TupleEmission) : Bool :=
  emission.origin.terms?.all fun terms => terms.size == emission.tuple.atoms.size

/-- Every tuple in the erased output has at least one recorded origin. Empty
    relations need no origin because they assert no positive tuple. -/
@[expose] public def TracedDataInstance.coversOutput (trace : TracedDataInstance) : Bool :=
  trace.data.relations.all fun relation =>
    relation.tuples.all fun tuple =>
      trace.emissions.any fun emission => emission.matches relation tuple

/-- Every recorded origin points back to a tuple in the erased output. -/
@[expose] public def TracedDataInstance.originsMatchOutput
    (trace : TracedDataInstance) : Bool :=
  trace.emissions.all fun emission =>
    trace.data.relations.any fun relation =>
      relation.tuples.any fun tuple => emission.matches relation tuple

/-- The executable structural invariant of a production trace. This does not
    yet validate the semantic meaning of an origin. -/
@[expose] public def TracedDataInstance.wellFormedTrace (trace : TracedDataInstance) : Bool :=
  trace.coversOutput && trace.originsMatchOutput &&
    trace.emissions.all (·.termsAligned) && trace.data.tuplesWellFormed

end SpytialLean
