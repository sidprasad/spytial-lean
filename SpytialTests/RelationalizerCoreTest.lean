module

public import SpytialLean.RelationalizerCore
meta import SpytialLean.RelationalizerCore

open SpytialLean SpytialLean.RelationalizerCore

namespace RelationalizerCoreTest

private def sample : RootedJsonDataInstance :=
  let (root, graph) := ({} : Graph).freshId
  let graph := graph.addAtom { id := root, type := "Box", label := "mk" }
  let (first, graph) := graph.freshId
  let graph := graph.addAtom { id := first, type := "Nat", label := "1" }
  let graph := graph.addField "value" root "Box" first "Nat"
  let (second, graph) := graph.freshId
  let graph := graph.addAtom { id := second, type := "Nat", label := "2" }
  let graph := graph.addField "value" root "Box" second "Nat"
  let graph := graph.addRelation "empty" #["Box", "Nat"]
  { root, data := graph.toDataInstance }

private def sameNamedFields : JsonDataInstance :=
  let graph := ({} : Graph).addField "value" "a" "A" "one" "Nat"
  let graph := graph.addField "value" "b" "B" "two" "Nat"
  let graph := graph.addRelation "value" #["Empty", "Nat"] (fieldRelationId "Empty" "value")
  graph.toDataInstance

example : sameNamedFields.relations.size = 3 := by native_decide

example : (sameNamedFields.relations.all (·.name == "value")) = true := by native_decide

example : (sameNamedFields.relations.any fun r =>
    r.id == fieldRelationId "A" "value" && r.tuples.map (·.atoms) == #[#["a", "one"]]) = true := by
  native_decide

example : (sameNamedFields.relations.any fun r =>
    r.id == fieldRelationId "B" "value" && r.tuples.map (·.atoms) == #[#["b", "two"]]) = true := by
  native_decide

example : (sameNamedFields.relations.any fun r =>
    r.id == fieldRelationId "Empty" "value" && r.tuples.isEmpty) = true := by native_decide

example : fieldRelationId "A:B" "C" ≠ fieldRelationId "A" "B:C" := by decide_cbv

private def identityAllocations : Array Allocation :=
  let engine : Engine String String := Engine.empty
  let (first, engine) := engine.intern (.keyed "Nat" "1")
  let (same, engine) := engine.intern (.keyed "Nat" "1")
  let (otherType, engine) := engine.intern (.keyed "OtherNat" "1")
  let (writtenOnce, engine) := engine.intern .asWritten
  let (writtenTwice, _) := engine.intern .asWritten
  #[first, same, otherType, writtenOnce, writtenTwice]

private def sharedFields : RootedJsonDataInstance :=
  walk <| .value .asWritten "Pair" "mk" [
    ("first", .value (.keyed "Nat" "one") "Nat" "1" []),
    ("second", .value (.keyed "Nat" "one") "Nat" "1" [])
  ]

private def writtenFields : RootedJsonDataInstance :=
  walk (.value .asWritten "Pair" "mk" [
    ("first", .value .asWritten "Nat" "1" []),
    ("second", .value .asWritten "Nat" "1" [])
  ] : Node String String)

example : sample.root = "atom_0" := by native_decide
example : sample.data.atoms.map (fun atom => atom.id) = #["atom_0", "atom_1", "atom_2"] := by
  native_decide

example : (sample.data.relations.any fun relation =>
    relation.name == "value" &&
      relation.types == #["Box", "Nat"] &&
      relation.tuples.map (fun tuple => tuple.atoms) ==
        #[#["atom_0", "atom_1"], #["atom_0", "atom_2"]]) = true := by
  native_decide

example : (sample.data.relations.any fun relation =>
    relation.name == "empty" && relation.tuples.isEmpty) = true := by
  native_decide

example : identityAllocations = #[
    .fresh "atom_0",
    .reused "atom_0",
    .fresh "atom_1",
    .fresh "atom_2",
    .fresh "atom_3"
  ] := by
  native_decide

example : sharedFields.data.atoms.size = 2 := by native_decide

example : writtenFields.data.atoms.size = 3 := by native_decide

private def traversalEvents : Array String :=
  let record (event : String) : StateM (Array String) Unit :=
    modify (·.push event)
  let fields := visitFields
    (fun name => do
      record s!"expose:{name}"
      return if name == "skip" then none else some (name, name))
    (fun child => do
      record s!"visit:{child}"
      return ⟨s!"id:{child}"⟩)
    (fun child => do
      record s!"type:{child}"
      return ⟨"Nat"⟩)
    (fun name owner ownerType child childType =>
      record s!"edge:{name}:{owner}:{ownerType}:{child}:{childType}")
    "root" "Pair" ["left", "skip", "right"]
  (emitStructure (fun atom => record s!"atom:{atom.id}")
    { id := "root", type := "Pair", label := "mk" } fields).run #[] |>.2

/-- Effects remain depth-first and left-to-right; skipped fields never recurse or emit edges. -/
example : traversalEvents = #[
    "atom:root", "expose:left", "visit:left", "type:left",
    "edge:left:root:Pair:id:left:Nat", "expose:skip",
    "expose:right", "visit:right", "type:right", "edge:right:root:Pair:id:right:Nat"] := by
  decide_cbv

/-- Reuse must not visit an otherwise different descendant: custom identity semantics are unchanged. -/
private def reusedSubtree : RootedJsonDataInstance :=
  walk (.value .asWritten "Pair" "mk" [
    ("left", .value (.keyed "Box" "same") "Box" "mk"
      [("value", .value .asWritten "Nat" "1" [])]),
    ("right", .value (.keyed "Box" "same") "Box" "mk"
      [("value", .value .asWritten "Nat" "2" [])])
  ] : Node String String)

example : reusedSubtree.data.atoms.map (·.label) = #["mk", "mk", "1"] := by
  native_decide

end RelationalizerCoreTest
