module

public import Lean

namespace SpytialLean

open Lean

/-- A single atom (node) in the relational data instance. -/
public meta structure JsonAtom where
  id : String
  type : String
  label : String
  deriving ToJson, FromJson, Inhabited

/-- A tuple in a relation — an ordered list of atom IDs with their types. -/
public meta structure JsonTuple where
  atoms : Array String
  types : Array String
  deriving ToJson, FromJson, Inhabited

/-- A relation (edge type) with its tuples. -/
public meta structure JsonRelation where
  id : String
  name : String
  types : Array String
  tuples : Array JsonTuple
  deriving ToJson, FromJson, Inhabited

/-- A complete relational data instance, matching spytial-core's `IJsonDataInstance`.
    See spytial-core/src/data-instance/json-data-instance.ts:33-40 -/
public meta structure JsonDataInstance where
  atoms : Array JsonAtom
  relations : Array JsonRelation
  deriving ToJson, FromJson, Inhabited

end SpytialLean
