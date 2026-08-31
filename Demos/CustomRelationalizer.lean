import SpytialLean

open SpytialLean
open Lean Meta

/-! # Custom Relationalizer -/

structure SimpleGraph where
  vertices : List String
  edges : List (String × String)

/-- A node per vertex and an edge per `(src, dst)` pair, in place of the
    internal `List` structure. -/
def relationalizeSimpleGraph : CustomRelationalizer := fun e _walkExpr => do
  let e ← Meta.whnf e

  let verticesExpr ← Meta.whnf (← Meta.mkProjection e `vertices)
  let edgesExpr ← Meta.whnf (← Meta.mkProjection e `edges)

  let s ← get
  let (graphId, s) := s.freshId
  set s
  modify fun s => s.addAtom { id := graphId, type := "SimpleGraph", label := "graph" }

  let mut vertexIds : Std.HashMap String String := {}
  let mut cur := verticesExpr
  while true do
    let cur' ← Meta.whnf cur
    match cur'.getAppFn with
    | .const ``List.cons _ =>
      let args := cur'.getAppArgs
      if args.size ≥ 3 then
        let headExpr ← Meta.whnf args[1]!
        let label ← ppLabel headExpr
        let s ← get
        let (vid, s) := s.freshId
        set s
        modify fun s => s.addAtom { id := vid, type := "vertex", label := label }
        modify fun s => s.addTuple "vertex" #["SimpleGraph", "vertex"]
          { atoms := #[graphId, vid], types := #["SimpleGraph", "vertex"] }
        vertexIds := vertexIds.insert label vid
        cur := args[2]!
      else break
    | _ => break

  cur := edgesExpr
  while true do
    let cur' ← Meta.whnf cur
    match cur'.getAppFn with
    | .const ``List.cons _ =>
      let args := cur'.getAppArgs
      if args.size ≥ 3 then
        let pairExpr ← Meta.whnf args[1]!
        let srcExpr ← Meta.whnf (← Meta.mkProjection pairExpr `fst)
        let dstExpr ← Meta.whnf (← Meta.mkProjection pairExpr `snd)
        let srcLabel ← ppLabel srcExpr
        let dstLabel ← ppLabel dstExpr
        if let (some srcId, some dstId) := (vertexIds.get? srcLabel, vertexIds.get? dstLabel) then
          modify fun s => s.addTuple "edge" #["vertex", "vertex"]
            { atoms := #[srcId, dstId], types := #["vertex", "vertex"] }
        cur := args[2]!
      else break
    | _ => break

  return graphId

spytial_relationalizer SimpleGraph relationalizeSimpleGraph

def myGraph : SimpleGraph :=
  { vertices := ["A", "B", "C", "D"]
    edges := [("A", "B"), ("B", "C"), ("C", "A"), ("A", "D")] }

#spytial myGraph
#spytial.datum myGraph
