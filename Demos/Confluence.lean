import SpytialLean

open SpytialLean

/-!
# Confluence: completing a strip under partial knowledge

The carrier and reduction relation stay arbitrary. A solid edge is one `step`; a dashed
`steps` edge is a proved sequence of zero or more steps with an unknown interior. Neither
the vertices nor those interiors are computed, enumerated, or chosen to make a picture.

The interesting proof is `strip`: move a single step across an arbitrary sequence. Each
inspection precedes a decision about which hypothesis to apply or which paths to compose.
`diamond_confluent` then uses the strip lemma to join two arbitrary sequences.

The assumption is the diamond property with one step on each lower side, not mere local
confluence. Local confluence alone does not imply confluence without further assumptions.
Different vertex names do not assert distinctness. Missing edges assert nothing, and the
goal's as-yet-unproved edges are not part of any inspection.
-/

namespace ConfluenceDemo

variable {α : Type} {step : α → α → Prop}

/-- Reflexive transitive closure, with the first step exposed by induction. -/
inductive Steps (step : α → α → Prop) : α → α → Prop where
  | refl (a) : Steps step a a
  | cons {a p b} : step a p → Steps step p b → Steps step a b

/-- Every pair of single steps can be completed by two single steps. -/
def Diamond (step : α → α → Prop) : Prop :=
  ∀ ⦃a b c⦄, step a b → step a c → ∃ d, step b d ∧ step c d

/-- Any two finite reduction sequences from a common source can be joined. -/
def Confluent (step : α → α → Prop) : Prop :=
  ∀ ⦃a b c⦄, Steps step a b → Steps step a c →
    ∃ d, Steps step b d ∧ Steps step c d

-- This macro supplies presentation only; the inspected facts come from the current proof.
-- Proposition-valued relation parameters are omitted from the displayed tuples, so both
-- `step` and `Steps` are binary. Align the path segments that have not been composed yet.
set_option hygiene false in
local macro "draw_reductions " t:term : tactic =>
  `(tactic| spytial $t with [
    size univ 72 44,
    atomStyle (borderStyle "#64748b" 1) (fillStyle "#f8fafc"),
    edgeStyle Steps (lineStyle "#2563eb" dashed) noLabels,
    edgeStyle step (lineStyle "#334155" solid) noLabels,
    orientation step - iden below,
    orientation Steps - iden right,
    align ~step.step - iden horizontal,
    align Steps - step.Steps - iden horizontal,
    orientation (~step.step & ((Steps - step.Steps).univ -> univ)) - iden left,
    align step & (univ.Steps -> univ.Steps) vertical
  ])

/-- A single step can be moved across an arbitrary sequence of steps. -/
theorem strip (diamond : Diamond step) {a b c : α}
    (hab : Steps step a b) (hac : step a c) :
    ∃ d, step b d ∧ Steps step c d := by
  induction hab generalizing c with
  | refl a =>
      exact ⟨c, hac, .refl c⟩
  | @cons a p b hap hpb ih =>
      -- 1. Known: a → p ⇝ b and a → c. The goal asks for a common successor of b and c.
      -- The induction hypothesis starts at p, so hac (which starts at a) cannot feed it.
      -- The two single steps out of a are exactly the premises of `diamond`.
      draw_reductions a
      obtain ⟨q, hpq, hcq⟩ := diamond hap hac

      -- 2. Known additionally: p → q and c → q, sharing the SAME witness q.
      -- Now p ⇝ b and p → q match ih. hcq starts at c and would be the wrong argument.
      draw_reductions a
      obtain ⟨d, hbd, hqd⟩ := ih hpq

      -- 3. Known additionally: b → d and q ⇝ d. The goal needs c ⇝ d.
      -- Read the route c → q ⇝ d: prepend hcq to hqd. No path interior is inspected.
      draw_reductions a
      have hcd : Steps step c d := .cons hcq hqd

      -- 4. The completed strip: b → d and c ⇝ d use the SAME final witness d.
      draw_reductions a
      exact ⟨d, hbd, hcd⟩

/-- The diamond property implies confluence, by repeatedly completing strips. -/
theorem diamond_confluent (diamond : Diamond step) : Confluent step := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl a =>
      exact ⟨c, hac, .refl c⟩
  | @cons a p b hap hpb ih =>
      -- Strip across the OTHER sequence a ⇝ c using the single step a → p.
      obtain ⟨q, hcq, hpq⟩ := strip diamond hac hap
      -- The remaining fork starts at p: p ⇝ b and p ⇝ q.
      obtain ⟨d, hbd, hqd⟩ := ih hpq
      exact ⟨d, hbd, .cons hcq hqd⟩

end ConfluenceDemo
