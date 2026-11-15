import Mathlib.Combinatorics.SimpleGraph.Acyclic
import SpytialLean

open SpytialLean

/-!
# An actual stuck proof: two paths with different first hops

Adapted from Leo Shine's unfinished proof, posted to Lean Zulip on 27 November 2025:
https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Problem.20proving.20statements.20about.20graphs.html#560666818

The statement and proof strategy are the author's. For mathlib v4.33.1, the two
edge-connectivity definitions are already in mathlib with identical bodies, and
`G.loopless w h3` becomes `G.irrefl h3`. The old path-uniqueness and mapLe lemma
aliases are deliberately retained so the remaining proof follows the posted text.
The only mathematical addition is the final line replacing the author's hole.
Three inspections have been added; neither their macros nor the inspections
change any goal or add mathematical hypotheses.

In the route view, solid arrows are known first edges, directed along the walk.
Red means the edge is proved absent after deletion; green means proved present.
Grey dashed arrows are walk tails with unknown interiors (possibly empty).
Blue dashed arrows assert surviving reachability without choosing a route.
The diagram is partial: missing edges assert nothing. Separate vertex names do
not by themselves assert inequality; here `wne` explicitly proves w' ≠ w.

The first-vertex view projects known Walk.cons nodes onto their next vertex;
`mapLe` preserves it. The red dotted relation is a proved inequality, not a graph edge.
The fields u, v, w below are the START, NEXT, and END constructor arguments of Walk.cons;
these field names are independent of the user's local vertex names.

This is a retrospective demonstration, not a claim that the author used Spytial.
Vlad Tsyrklevich's actual reply instead gave a shorter proof using the IsBridge API.
-/

set_option linter.unusedTactic false

-- Presentation only: relational composition reads endpoints from known Walk.cons nodes.
set_option hygiene false in
local macro "draw_routes " paths:term : tactic =>
  `(tactic| spytial $paths with [
    hideAtom univ - lean (fun _ : V => True),
    hideField Adj, hideField Reachable,
    size univ 70 44,
    orientation ~u.v right,
    orientation ~v.w - iden right,
    align ~u.w horizontal,
    orientation ~u.v & lean (fun x y : V => ¬ (G.deleteEdges s1).Adj x y) above,
    orientation ~u.v & lean (fun x y : V => (G.deleteEdges s1).Adj x y) below,
    inferredEdge first ~u.v & lean (fun x y : V => (G.deleteEdges s1).Adj x y)
      (lineStyle "#15803d" solid),
    inferredEdge deleted ~u.v & lean (fun x y : V => ¬ (G.deleteEdges s1).Adj x y)
      (lineStyle "#b91c1c" solid),
    inferredEdge tail ~v.w - iden (lineStyle "#64748b" dashed),
    inferredEdge survives lean (fun x y : V => (G.deleteEdges s1).Reachable x y)
      (lineStyle "#2563eb" dashed)
  ])

set_option hygiene false in
local macro "draw_first_vertices " paths:term : tactic =>
  `(tactic| spytial $paths with [
    hideAtom univ - (u.univ + univ.v),
    hideField Adj, hideField Reachable, hideField v, hideField IsPath,
    size univ 100 48,
    orientation v right,
    align v horizontal,
    align u.~u - iden vertical,
    inferredEdge first_vertex v (lineStyle "#334155" solid),
    inferredEdge different lean (fun x y : V => x ≠ y) (lineStyle "#b91c1c" dotted),
    atomStyle u.univ (fillStyle "#eff6ff") (borderStyle "#2563eb" 2),
    atomStyle univ.v (fillStyle "#fefce8") (borderStyle "#a16207" 2)
  ])

namespace SimpleGraph
variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')
open Walk
theorem IsAcyclic.not_twoConnected_inspected (h : G.IsAcyclic) (u : V) (v : V) (hunev : u ≠ v)
    : ¬ G.IsEdgeConnected 2 := by
  by_contra hconn
  specialize hconn u v
  by_cases h2 : G.Reachable u v
  · obtain ⟨ p1: G.Walk u v, hp1⟩  := (Reachable.exists_isPath h2)
    match hp1eq : p1 with
    | nil => contradiction
    | cons' _ w vvv huw p =>
      let s1 := ({s(u,w)} : Set (Sym2 V))
      have hv : v = vvv:= by assumption
      subst hv
      have hsletwo : s1.encard < 2 := by
        unfold s1
        simp
      have hdeladj: ¬(G.deleteEdges s1).Adj u w :=by
            unfold s1
            unfold deleteEdges
            unfold Adj
            simp
            intro h3 h4
            rw [h4] at h3
            exact G.irrefl h3
      specialize hconn hsletwo
      obtain ⟨ p2: (G.deleteEdges s1).Walk u v, hp2⟩  := (Reachable.exists_isPath hconn)
      -- A route survives, but its first hop and interior are still unknown.
      draw_routes (p1, p2)
      -- use isAcyclic_iff_path_unique paths then show path having removed an edge in the first path
      -- from the graph is not equal
      match hp2eq : p2 with
      | nil => contradiction
      | cons' _ w' vv huw' prst =>
        have wne : w' ≠ w:= by
          by_contra hweq
          rw[← hweq] at hdeladj
          contradiction
        let p3 := p2.mapLe (deleteEdges_le s1)
        have hv : v = vv:= by assumption
        subst hv
        -- The surviving route starts at w', with wne : w' ≠ w.
        draw_routes (p1, p2)
        -- mapLe has preserved that first vertex; both paths now live in G.
        draw_first_vertices (p1, p3)
        have hp2eq:  p2 = cons huw' prst := by
          cases hp2eq
          simp
        have hp1eq:  p1 = cons huw p := by
          cases hp1eq
          simp
        have hp1: p1.IsPath := by
          unfold cons' at hp1
          rw[hp1eq]
          assumption
        have hp3 : p3.IsPath := by
          refine (mapLe_isPath (deleteEdges_le s1)).mpr ?_
          unfold cons' at hp2
          rw[hp2eq]
          assumption
        rw[isAcyclic_iff_path_unique] at h
        specialize h ⟨p3, hp3⟩ ⟨p1, hp1⟩
        -- Now prove not the same
        have h: p3 = p1 := by simpa using h
        rw[← h] at hp1eq
        unfold p3 at hp1eq
        rw[hp2eq] at hp1eq
        unfold mapLe at hp1eq
        unfold Walk.map at hp1eq
        -- This is the author's original stopping point. Comparing the next vertices
        -- finishes the proof; adding spytial here reports an inconsistent context.
        exact wne (by simpa using congrArg Walk.snd hp1eq)
  · have hempt: (∅ : Set (Sym2 V)).encard < 2 := by
      simp
    specialize hconn  hempt
    rw[deleteEdges_empty] at hconn
    contradiction

end SimpleGraph
