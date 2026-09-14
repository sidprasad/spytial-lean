module

public import Lean

namespace SpytialLean

open Lean

/-- Stable structural-field identity. Escape the owner component to prevent delimiter collisions.
Selectors use the separate relation name; reification uses this ID. -/
@[expose] public def fieldRelationId (ownerType name : String) : String :=
  "lean:field:" ++ String.ofList (ownerType.toList.flatMap fun c =>
    if c == ':' || c == '\\' then ['\\', c] else [c]) ++ ":" ++ name

-- Keep kernel evaluation on character lists and string primitives, including across module imports.
@[cbv_eval] public theorem fieldRelationId_eq (ownerType name : String) :
    fieldRelationId ownerType name =
      "lean:field:" ++ String.ofList (ownerType.toList.flatMap fun c =>
        if c == ':' || c == '\\' then ['\\', c] else [c]) ++ ":" ++ name := rfl

public theorem fieldRelationId_injective (ownerType : String) :
    Function.Injective (fieldRelationId ownerType) := by
  intro left right equality
  exact (String.append_right_inj _).mp equality

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

/-- A relation identity, its selector name, and its known tuples. -/
public structure JsonRelation where
  /-- Storage and reconstruction identity, independent of the selector name. -/
  id : String
  /-- Selectors denote the tuple set union of all records with this name. -/
  name : String
  types : Array String
  tuples : Array JsonTuple
  deriving ToJson, FromJson, Inhabited

/-- The relational data instance passed to Spytial's rendering pipeline. -/
public structure JsonDataInstance where
  atoms : Array JsonAtom
  relations : Array JsonRelation
  deriving ToJson, FromJson, Inhabited

/-- A relational data instance together with the ID of its distinguished root atom.

The underlying relational instance may contain many values and is not inherently rooted. This
wrapper records which atom denotes the host-language value being transported. -/
public structure RootedJsonDataInstance where
  root : String
  data : JsonDataInstance
  deriving ToJson, FromJson, Inhabited

end SpytialLean
