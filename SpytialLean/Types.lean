module

public import Lean

namespace SpytialLean

open Lean

/-- A single atom in the relational data instance consumed by Spytial. -/
public meta structure JsonAtom where
  id : String
  type : String
  label : String
  deriving ToJson, FromJson, Inhabited

/-- A tuple in a relation: an ordered list of atom IDs with their types. -/
public meta structure JsonTuple where
  atoms : Array String
  types : Array String
  deriving ToJson, FromJson, Inhabited

/-- A named relation and its known tuples. -/
public meta structure JsonRelation where
  id : String
  name : String
  types : Array String
  tuples : Array JsonTuple
  deriving ToJson, FromJson, Inhabited

/-- The relational data instance passed to Spytial's rendering pipeline. -/
public meta structure JsonDataInstance where
  atoms : Array JsonAtom
  relations : Array JsonRelation
  deriving ToJson, FromJson, Inhabited

end SpytialLean
