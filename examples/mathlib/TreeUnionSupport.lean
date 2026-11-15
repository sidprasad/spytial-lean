/-
Adapted from mathlib PR #35327 by Snir Broshi.
Released under Apache 2.0; see mathlib's LICENSE.
https://github.com/leanprover-community/mathlib4/pull/35327
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SimpleGraph
namespace Walk
variable {V : Type*}
/-- Given two walks `p₁` `p₂` connecting `u` to `v` to `w`, and darts `d₁` `d₂` in the walks,
if the first dart ends where the second dart begins and there's only one appearance of that vertex
in the concatenation of the two walks, then those darts must be adjacent to the `v` vertex that
connects the two walks. -/
theorem lastDart_eq_of_count_support_append_eq_one [DecidableEq V] {G : SimpleGraph V} {u v w : V}
    {p₁ : G.Walk u v} {p₂ : G.Walk v w} {d₁ d₂ : G.Dart} (hd₁ : d₁ ∈ p₁.darts) (hd₂ : d₂ ∈ p₂.darts)
    (hd : d₁.snd = d₂.fst) (hc : (p₁.append p₂).support.count d₁.snd = 1) :
    p₁.lastDart (by cases p₁ <;> simp_all) = d₁ := by
  rw [lastDart_eq_getLast_darts]
  have := List.mem_append.mp <| p₁.darts.dropLast_concat_getLast (List.ne_nil_of_mem hd₁) ▸ hd₁
  refine (List.mem_singleton.mp <| this.resolve_left fun hd₁' ↦ ?_).symm
  rw [p₁.support_append_eq_support_dropLast_append p₂, List.count_append] at hc
  have := List.one_le_count_iff.mpr <| dart_fst_mem_support_of_mem_darts _ hd₂
  apply p₁.support.dropLast.not_mem_of_count_eq_zero (a := d₁.snd) <| by lia
  rw [← cons_map_snd_darts,
    List.dropLast_cons_of_ne_nil <| List.map_eq_nil_iff.not.mpr <| List.ne_nil_of_mem hd₁,
    List.mem_cons, ← List.map_dropLast]
  exact .inr <| List.mem_map_of_mem hd₁'

theorem firstDart_eq_of_count_support_append_eq_one [DecidableEq V] {G : SimpleGraph V} {u v w : V}
    {p₁ : G.Walk u v} {p₂ : G.Walk v w} {d₁ d₂ : G.Dart} (hd₁ : d₁ ∈ p₁.darts) (hd₂ : d₂ ∈ p₂.darts)
    (hd : d₁.snd = d₂.fst) (hc : (p₁.append p₂).support.count d₁.snd = 1) :
    p₂.firstDart (by cases p₂ <;> simp_all) = d₂ := by
  rw [firstDart_eq_head_darts]
  have := List.mem_cons.mp <| p₂.darts.cons_head_tail (List.ne_nil_of_mem hd₂) ▸ hd₂
  refine (this.resolve_right fun hd₂' ↦ ?_).symm
  rw [p₁.support_append p₂, List.count_append] at hc
  have := List.one_le_count_iff.mpr <| dart_snd_mem_support_of_mem_darts _ hd₁
  apply p₂.support.tail.not_mem_of_count_eq_zero (a := d₂.fst) <| by lia
  rw [← map_fst_darts_append,
    List.tail_append_of_ne_nil <| List.map_eq_nil_iff.not.mpr <| List.ne_nil_of_mem hd₂,
    List.mem_append, ← List.map_tail]
  exact .inl <| List.mem_map_of_mem hd₂'

end Walk

open Walk
variable {V : Type*} {G : SimpleGraph V}
/-- The union of two acyclic graphs that share at most one vertex is acyclic. -/
theorem IsAcyclic.coe_sup {G₁ G₂ : G.Subgraph} (h₁ : G₁.coe.IsAcyclic) (h₂ : G₂.coe.IsAcyclic)
    (h : (G₁.verts ∩ G₂.verts).Subsingleton) : (G₁ ⊔ G₂).coe.IsAcyclic := by
  intro v p hp
  -- If the cycle is entirely contained within one of the subgraphs
  by_cases! hp' : (∀ u ∈ p.support, u.val ∈ G₁.verts) ∨ (∀ u ∈ p.support, u.val ∈ G₂.verts)
  · -- WLOG it's contained in the first one
    wlog hp'₁ : ∀ u ∈ p.support, u.val ∈ G₁.verts
    · have hp'₂ := hp'.resolve_left hp'₁
      let p' := p.map <| Subgraph.inclusion <| sup_comm G₁ G₂ |>.le
      have hp' : ∀ u ∈ p'.support, u.val ∈ G₂.verts := fun u hu ↦ by
        obtain ⟨u', hu', rfl⟩ := p.support.mem_map.mp <| p.support_map _ ▸ hu
        exact hp'₂ u' hu'
      exact this h₂ h₁ (Set.inter_comm G₁.verts G₂.verts ▸ h) p'
        (hp.map <| Subgraph.inclusion.injective _) (.inl hp') hp'
    -- Then it must be induced from a walk in the first graph
    let p' := p.map (G₁ ⊔ G₂).hom
    have hp' : p'.IsCycle := hp.map Subgraph.hom_injective
    let p'' := p'.mapToSubgraph.map <| Subgraph.inclusion <|
      toSubgraph_le_iff hp'.not_nil (G' := G₁) |>.mpr fun e he ↦ by
        obtain ⟨⟨u, v⟩, he', rfl⟩ := p.edges.mem_map.mp <| p.edges_map _ ▸ p'.mem_edgeSet.mp he
        refine G₁.edgeSet_sup ▸ Subgraph.edgeSet_coe ▸ p.edges_subset_edgeSet he' |>.elim id ?_
        refine fun he₂ ↦ False.elim <| he₂.ne <| h ?_ ?_
        · exact ⟨hp'₁ u <| p.fst_mem_support_of_mem_edges he', he₂.fst_mem⟩
        · exact ⟨hp'₁ v <| p.snd_mem_support_of_mem_edges he', he₂.snd_mem⟩
    -- And that walk is also a cycle, but the first graph is acyclic, contradiction
    exact h₁ p'' <| IsCycle.map (Subgraph.inclusion.injective _) <|
      isCycle_map_iff_of_injective p'.toSubgraph.hom_injective |>.mp <|
      map_mapToSubgraph_hom _ ▸ hp'
  -- Otherwise, there are two vertices in the cycle, each not contained in one of the graphs
  have ⟨⟨v₂, hpv₂, hnv₂⟩, ⟨v₁, hpv₁, hnv₁⟩⟩ := hp'
  have hv₂ := v₂.prop.resolve_left hnv₂
  classical
  -- Consider the walk `pt` from `v₁` to `v₂` and the walk `pd` from `v₂` back to `v₁`
  let p' := p.rotate v₁ hpv₁
  have hp'v₂ := p.mem_support_rotate_iff v₁ hpv₁ |>.mpr hpv₂
  let pt := p'.takeUntil v₂ hp'v₂
  let pd := p'.dropUntil v₂ hp'v₂
  -- Each must have a dart that crosses to the other subgraph
  have ⟨d₁, hd₁, hd₁₁, hd₁₂⟩ := pt.exists_boundary_dart { v | v.val ∉ G₂.verts } hnv₁ (· hv₂)
  have ⟨d₂, hd₂, hd₂₁, hd₂₂⟩ := pd.exists_boundary_dart { v | v.val ∈ G₂.verts } hv₂ hnv₁
  -- `d₁.snd` and `d₂.fst` are common to both subgraphs so must be equal
  have hd₁₂' : d₁.snd.val ∈ G₁.verts ∩ G₂.verts :=
    ⟨d₁.edge_mem.resolve_right (hd₁₁ ·.fst_mem) |>.snd_mem, Set.not_notMem.mp hd₁₂⟩
  have hd₂₁' : d₂.fst.val ∈ G₁.verts ∩ G₂.verts :=
    ⟨d₂.edge_mem.resolve_right (hd₂₂ ·.snd_mem) |>.fst_mem, hd₂₁⟩
  have hd₁₂'' := p'.dart_snd_mem_support_of_mem_darts <| p'.darts_takeUntil_subset_darts hp'v₂ hd₁
  -- Since `d₁.snd` and `d₂.fst` are on a cycle, that vertex can only appear once,
  -- so `d₁`/`d₂` must be the last/first dart of `pt`/`pd` respectively
  have hpd := firstDart_eq_of_count_support_append_eq_one hd₁ hd₂ (Subtype.ext <| h hd₁₂' hd₂₁') <|
    p'.take_spec hp'v₂ ▸ (hp.rotate hpv₁).count_support_of_mem hd₁₂'' (hd₁₂ <| · ▸ hnv₁)
  -- But that means that `d₁`/`d₂` are to/from `v₂` respectively,
  -- so `v₂` is in both subgraphs and in particular it is in `G₁`, contradiction
  exact hnv₂ <| (hpd ▸ rfl : v₂ = d₂.fst) ▸ hd₂₁'.left

/-- The union of two trees that share exactly one vertex is a tree. -/
theorem IsTree.coe_sup {G₁ G₂ : G.Subgraph} (h₁ : G₁.coe.IsTree) (h₂ : G₂.coe.IsTree) {v : V}
    (h : G₁.verts ∩ G₂.verts = {v}) : (G₁ ⊔ G₂).coe.IsTree where
  connected := Subgraph.connected_sup ⟨h₁.preconnected⟩ ⟨h₂.preconnected⟩ <| by simp [h]
  isAcyclic := .coe_sup h₁.isAcyclic h₂.isAcyclic <| by simp [h]

end SimpleGraph
