/-
Original proof: Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0: https://github.com/leanprover-community/mathlib4/blob/master/LICENSE
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import SpytialLean

open SpytialLean

/-!
# Which edge can the forest add?

A forest `F` uses edges of a graph `G`. Every remaining edge of `G` would
create a cycle if added to `F`. Could two vertices still be connected in `G`
and disconnected in `F`?

Follow the two `draw_cut` calls in mathlib's proof. The boxes classify the
vertices we know about by membership in one component of `F`. The dashed line
means there is a walk in `G`. The solid line is one known edge along that walk.

Source: [mathlib v4.33.1, Acyclic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.1/Mathlib/Combinatorics/SimpleGraph/Acyclic.lean#L395).
-/

set_option linter.unusedTactic false

set_option hygiene false in
local macro "draw_cut " vertices:term : tactic =>
  `(tactic| spytial $vertices with [
    hideAtom univ - lean (fun _ : V => True),
    hideField Adj,
    hideField Reachable,
    size univ 78 42,
    group lean (fun x : V => x = u ∨ x ∈ s) "Component of u in F",
    group lean (fun x : V => x ∉ s) "Outside that component",
    orientation lean (fun x y : V => (x = u ∨ x ∈ s) ∧ y ∉ s) right,
    align lean (fun x y : V => G.Reachable x y) horizontal,
    align lean (fun x y : V => G.Adj x y) horizontal,
    inferredEdge walk lean (fun x y : V => G.Reachable x y)
      (lineStyle "#2563eb" dashed),
    inferredEdge edge lean (fun x y : V => G.Adj x y) (lineStyle "#334155" solid),
    atomStyle (borderStyle "#475569" 1) (fillStyle "#ffffff")
  ])

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma reachable_eq_of_maximal_isAcyclic_inspected (F : SimpleGraph V)
    (h : Maximal (fun H ↦ H ≤ G ∧ H.IsAcyclic) F) : F.Reachable = G.Reachable := by
  ext u v
  refine ⟨.mono h.prop.left, fun ⟨p⟩ ↦ ?_⟩
  by_contra
  let s : F.ConnectedComponent := .mk _ u
  have : v ∉ s := this ∘ s.reachable_of_mem_supp rfl
  -- The walk ends outside u's component. What must happen somewhere along it?
  draw_cut (u, v)
  have : ∃ d ∈ p.darts, d.fst ∈ s ∧ d.snd ∉ s := p.exists_boundary_dart s rfl this
  rcases this with ⟨⟨⟨u', v'⟩, huv⟩, _, hu, hv⟩
  -- Which edge could F add? What would a cycle through that edge require?
  draw_cut (u, u', v', v)
  have : ¬F.Reachable v' u' := mt ConnectedComponent.sound <| s.mem_supp_iff u' |>.mp hu ▸ hv
  suffices F ⊔ edge v' u' ≤ F by grind [Adj.reachable, sup_le_iff, le_iff_adj]
  refine h.le_of_ge ⟨?_, h.prop.right.sup_edge_of_not_reachable this⟩ le_sup_left
  grind [Maximal, sup_le, le_iff_adj, huv.symm]

end SimpleGraph
