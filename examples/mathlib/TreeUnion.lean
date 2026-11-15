import TreeUnionSupport
import SpytialLean

open SimpleGraph SpytialLean

/-!
# Combining two routing trees: what did "union" activate?

Motivating use: two loop-free routing domains share one gateway. Combining their
chosen links preserves a tree. Selecting all their routers and inducing from the
physical network can silently activate a cross-link and introduce a cycle.

This is a new demonstration motivated by the mathematical error identified in
mathlib PR #35327, not a claim that its author used Spytial. The general tree-union
proof in TreeUnionSupport is adapted from that PR. The diagnostic theorem below
uses mathlib's existing graphs, subgraphs, trees, and reachability throughout.

The four inspections retain arbitrary trees and symbolic vertices. Dashed arrows
are proved routes with unknown interiors, not invented direct links. The first
view makes NO assertion about a cross-link. The second assumes one while inspecting
the troublesome case. The third proves that this link is outside the actual union.
The fourth inspects the corrected edge union, whose tree property has been proved.
Boxes contain only the known vertices in each region; they do not enumerate it.
Arrow directions follow the proof witnesses; the underlying graphs are undirected.
-/

set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false

namespace TreeUnion

-- A single shared presentation adapter. No graph is recreated for the diagram.
set_option hygiene false in
local macro "inspect_merge " graph:term " at " vertices:term : tactic =>
  `(tactic| spytial $vertices with [
    hideAtom univ - lean (fun _ : V => True),
    hideField mem,
    size univ 110 52,
    atomStyle (borderStyle "#334155" 1) (fillStyle "#ffffff"),
    group lean (fun x : V => x ∈ L.verts ∧ x ∉ R.verts) "Left only",
    group lean (fun x : V => x ∈ L.verts ∧ x ∈ R.verts) "Shared gateway",
    group lean (fun x : V => x ∈ R.verts ∧ x ∉ L.verts) "Right only",
    inferredEdge left_route lean (fun x y : V => L.spanningCoe.Reachable x y)
      (lineStyle "#2563eb" dashed),
    inferredEdge right_route lean (fun x y : V => R.spanningCoe.Reachable x y)
      (lineStyle "#0f766e" dashed),
    inferredEdge ambient
      lean (fun x y : V => ($graph).Adj x y) -
        lean (fun x y : V => ($graph).Adj x y ∧ ¬ (L ⊔ R).Adj x y)
      (lineStyle "#b45309" solid),
    inferredEdge outside_union
      lean (fun x y : V => ($graph).Adj x y ∧ ¬ (L ⊔ R).Adj x y)
      (lineStyle "#b91c1c" solid),
    inferredEdge no_link lean (fun x y : V => ¬ ($graph).Adj x y) - iden
      (lineStyle "#b91c1c" dotted),
    orientation lean (fun x y : V => L.spanningCoe.Reachable x y) right above,
    orientation lean (fun x y : V => R.spanningCoe.Reachable x y) right below
  ])

variable {V : Type*} {G : SimpleGraph V}

/-- Inspect the case a vertex-induced merge admits but the actual union excludes. -/
theorem diagnose_cross_link (L R : G.Subgraph) (hub x y : V)
    (hL : L.coe.IsTree) (hR : R.coe.IsTree)
    (hshared : L.verts ∩ R.verts = {hub})
    (hxL : x ∈ L.verts) (hxR : x ∉ R.verts)
    (hyR : y ∈ R.verts) (hyL : y ∉ L.verts) :
    G.Adj x y →
      ((⊤ : G.Subgraph).induce (L.verts ∪ R.verts)).Adj x y ∧
        ¬ (L ⊔ R).Adj x y ∧ (L ⊔ R).coe.IsTree ∧
          ¬ (G.induce (L.verts ∪ R.verts)).IsAcyclic := by
  have hhub : hub ∈ L.verts ∩ R.verts := hshared ▸ Set.mem_singleton hub
  have hhubL := hhub.1
  have hhubR := hhub.2
  have left_route : L.spanningCoe.Reachable x hub :=
    (hL.preconnected ⟨x, hxL⟩ ⟨hub, hhubL⟩).map L.coeEmbeddingSpanningCoe.toHom
  have right_route : R.spanningCoe.Reachable hub y :=
    (hR.preconnected ⟨hub, hhubR⟩ ⟨y, hyR⟩).map R.coeEmbeddingSpanningCoe.toHom
  -- Only the two routes are known. The cross-link is still undecided.
  inspect_merge G at (x, hub, y)
  intro hxy
  have activated : ((⊤ : G.Subgraph).induce (L.verts ∪ R.verts)).Adj x y :=
    ⟨Or.inl hxL, Or.inr hyR, hxy⟩
  -- A physical cross-link is admitted by inducing on the combined vertex set.
  inspect_merge G at (x, hub, y)
  have excluded : ¬ (L ⊔ R).Adj x y := by
    rintro (hleft | hright)
    · exact hyL (L.edge_vert hleft.symm)
    · exact hxR (R.edge_vert hright)
  -- Neither constituent tree owns the edge. Keep the edge union, or rule it out.
  inspect_merge G at (x, hub, y)
  have merged_tree : (L ⊔ R).coe.IsTree := hL.coe_sup hR hshared
  -- Inspect the selected-edge network. The physical cross-link still exists in G.
  inspect_merge (L ⊔ R).spanningCoe at (x, hub, y)
  -- The visible route plus the extra edge really forces a cycle, for arbitrary trees.
  have induced_cyclic : ¬ (G.induce (L.verts ∪ R.verts)).IsAcyclic := by
    intro hac
    let vx : (L ⊔ R).verts := ⟨x, Or.inl hxL⟩
    let vy : (L ⊔ R).verts := ⟨y, Or.inr hyR⟩
    have hle : (L ⊔ R).coe ⊔ edge vx vy ≤ G.induce (L.verts ∪ R.verts) := by
      refine sup_le ?_ ((edge_le_iff _).mpr (Or.inr hxy))
      intro a b hab
      exact (L ⊔ R).adj_sub hab
    have hroute := merged_tree.preconnected vx vy
    rcases (isAcyclic_sup_fromEdgeSet_iff.mp (hac.anti hle)).2 hroute with heq | hadj
    · have hxy' : x = y := congrArg Subtype.val heq
      exact hxR (hxy'.symm ▸ hyR)
    · exact excluded hadj
  exact ⟨activated, excluded, merged_tree, induced_cyclic⟩

/-- Repair 1: combine the selected edges. Ambient cross-links are harmless. -/
theorem edge_union_isTree (L R : G.Subgraph) (hL : L.coe.IsTree) (hR : R.coe.IsTree)
    {hub : V} (hshared : L.verts ∩ R.verts = {hub}) : (L ⊔ R).coe.IsTree :=
  hL.coe_sup hR hshared

/-- No physical edge joins a vertex exclusive to A to a vertex exclusive to B. -/
def NoCrossEdges (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ G.Adj x y

/-- The missing hypothesis closes exactly the mixed-membership cases. -/
theorem induced_union_eq (A B : Set V) (hNoCross : NoCrossEdges G A B) :
    (⊤ : G.Subgraph).induce (A ∪ B) =
      (⊤ : G.Subgraph).induce A ⊔ (⊤ : G.Subgraph).induce B := by
  apply le_antisymm ?_ Subgraph.le_induce_union
  constructor
  · intro x hx
    exact hx
  · rintro x y ⟨hx, hy, hxy⟩
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · exact Or.inl ⟨hxA, hyA, hxy⟩
      · have hyB := hy.resolve_left hyA
        by_cases hxB : x ∈ B
        · exact Or.inr ⟨hxB, hyB, hxy⟩
        · exact (hNoCross x ⟨hxA, hxB⟩ y ⟨hyB, hyA⟩ hxy).elim
    · have hxB := hx.resolve_left hxA
      by_cases hyB : y ∈ B
      · exact Or.inr ⟨hxB, hyB, hxy⟩
      · have hyA := hy.resolve_right hyB
        exact (hNoCross y ⟨hyA, hyB⟩ x ⟨hxB, hxA⟩ hxy.symm).elim

/-- The repair is exact: these two graph constructions agree iff there are no cross-edges. -/
theorem induced_union_eq_iff (A B : Set V) :
    (⊤ : G.Subgraph).induce (A ∪ B) =
        (⊤ : G.Subgraph).induce A ⊔ (⊤ : G.Subgraph).induce B ↔
      NoCrossEdges G A B := by
  refine ⟨?_, induced_union_eq A B⟩
  intro heq x hx y hy hxy
  have hedge : ((⊤ : G.Subgraph).induce (A ∪ B)).Adj x y :=
    ⟨Or.inl hx.1, Or.inr hy.1, hxy⟩
  rw [heq] at hedge
  rcases hedge with hleft | hright
  · exact hy.2 hleft.2.1
  · exact hx.2 hright.1

/-- Repair 2: keep the induced construction and require the missing separation condition. -/
theorem induced_union_isTree (A B : Set V)
    (hA : (G.induce A).IsTree) (hB : (G.induce B).IsTree)
    {hub : V} (hshared : A ∩ B = {hub}) (hNoCross : NoCrossEdges G A B) :
    (G.induce (A ∪ B)).IsTree := by
  have hA' : ((⊤ : G.Subgraph).induce A).coe.IsTree := by
    simpa only [G.induce_eq_coe_induce_top] using hA
  have hB' : ((⊤ : G.Subgraph).induce B).coe.IsTree := by
    simpa only [G.induce_eq_coe_induce_top] using hB
  have htree := edge_union_isTree _ _ hA' hB' hshared
  have heq := congrArg (fun H : G.Subgraph => H.coe.IsTree) (induced_union_eq A B hNoCross)
  simpa only [G.induce_eq_coe_induce_top] using heq.mpr htree

/-- For induced trees meeting at one gateway, the diagram reveals the exact missing condition. -/
theorem induced_union_isTree_iff (A B : Set V)
    (hA : (G.induce A).IsTree) (hB : (G.induce B).IsTree)
    {hub : V} (hshared : A ∩ B = {hub}) :
    (G.induce (A ∪ B)).IsTree ↔ NoCrossEdges G A B := by
  refine ⟨?_, induced_union_isTree A B hA hB hshared⟩
  intro hUnion x hx y hy hxy
  have hA' : ((⊤ : G.Subgraph).induce A).coe.IsTree := by
    simpa only [G.induce_eq_coe_induce_top] using hA
  have hB' : ((⊤ : G.Subgraph).induce B).coe.IsTree := by
    simpa only [G.induce_eq_coe_induce_top] using hB
  have diagnosis := diagnose_cross_link _ _ hub x y hA' hB' hshared hx.1 hx.2 hy.1 hy.2 hxy
  exact diagnosis.2.2.2 hUnion.isAcyclic

namespace Counterexample

abbrev physical : SimpleGraph (Fin 3) := ⊤
def A : Set (Fin 3) := {0, 1}
def B : Set (Fin 3) := {1, 2}

theorem left_tree : (physical.induce A).IsTree := by
  have hedge : physical.Adj 0 1 := by decide
  have heq := congrArg (fun H : physical.Subgraph => H.coe.IsTree)
    (Subgraph.subgraphOfAdj_eq_induce hedge)
  have htree := heq.mp (IsTree.coe_subgraphOfAdj hedge)
  simpa only [A, physical.induce_eq_coe_induce_top] using htree

theorem right_tree : (physical.induce B).IsTree := by
  have hedge : physical.Adj 1 2 := by decide
  have heq := congrArg (fun H : physical.Subgraph => H.coe.IsTree)
    (Subgraph.subgraphOfAdj_eq_induce hedge)
  have htree := heq.mp (IsTree.coe_subgraphOfAdj hedge)
  simpa only [B, physical.induce_eq_coe_induce_top] using htree

theorem shared_gateway : A ∩ B = {1} := by
  ext v
  fin_cases v <;> simp [A, B]

theorem physical_has_cycle : ¬ physical.IsAcyclic := by
  let loop : physical.Walk 0 0 :=
    .cons (by decide) (.cons (by decide : physical.Adj 1 2)
      (.cons (by decide : physical.Adj 2 0) .nil))
  have hloop : loop.IsCycle := by
    simp [loop, Walk.cons_isCycle_iff, Walk.isPath_def]
  exact fun h => h loop hloop

theorem induced_merge_has_cycle : ¬ (physical.induce (A ∪ B)).IsAcyclic := by
  have hunion : A ∪ B = Set.univ := by
    ext v
    fin_cases v <;> simp [A, B]
  rw [hunion]
  exact fun h => physical_has_cycle (physical.induceUnivIso.isAcyclic_iff.mp h)

theorem edge_merge_is_tree :
    (((⊤ : physical.Subgraph).induce A) ⊔ (⊤ : physical.Subgraph).induce B).coe.IsTree := by
  apply edge_union_isTree
  · simpa only [physical.induce_eq_coe_induce_top] using left_tree
  · simpa only [physical.induce_eq_coe_induce_top] using right_tree
  · exact shared_gateway

theorem has_cross_link : ¬ NoCrossEdges physical A B := by
  intro h
  exact h 0 (by simp [A, B]) 2 (by simp [A, B]) (by decide)

end Counterexample
end TreeUnion
