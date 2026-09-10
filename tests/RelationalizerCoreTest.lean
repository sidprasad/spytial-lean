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

end RelationalizerCoreTest
