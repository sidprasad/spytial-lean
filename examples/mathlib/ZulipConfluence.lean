import Mathlib.Logic.Relation
import SpytialLean

open SpytialLean

/-!
# Inspecting the Church–Rosser theorem questioned on Zulip

Source: Yaël Dillies's proposed generalization, 17 August 2021:
https://leanprover-community.github.io/archive/stream/113488-general/topic/relation.2Echurch_rosser.html

The discussion asks whether the `ReflGen` in the hypothesis can become `ReflTransGen`.
That would assert that local confluence implies confluence, which is false in general.

The first proof below is mathlib v4.33.1's `Relation.church_rosser`, with ONLY two
`spytial f` lines inserted and its theorem renamed. There is no layout specification,
custom relationalizer, added mathematical fact, or redefinition of reachability.
This is a retrospective inspection of the existing proof, not a claim that the
Zulip author posted this proof attempt or used Spytial.

At the first inspection, the bottom fork consists of `hfb : r f b` and `hfa : r f a`.
The goal needs a common endpoint reachable from `e`, and at most one step from `b`.
Apply `h` to the two edges with the same source `f`. At the second inspection, the
new witness `c` is connected by `a →* c` and `b →? c`. Compose `e →* a →* c`.

`r` means one step; `ReflGen` means zero or one; `ReflTransGen` means zero or more.
The interiors of the latter paths remain unknown. An absent edge is not a proof
of non-reachability. Different names need not be distinct; repeated display names
in this unedited proof come from shadowing, not from equality.

The separate four-state counterexample below is newly formalized diagnostic
material. It proves that the proposed generalization itself is false, rather
than merely showing that one particular proof strategy fails.
-/

set_option linter.unusedTactic false

namespace ZulipConfluence

open Relation
open ReflTransGen ReflGen

variable {α : Type*} {r : α → α → Prop} {a b c : α}

theorem church_rosser_inspected
    (h : ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d)
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) : Join (ReflTransGen r) b c := by
  induction hab with
  | refl => exact ⟨c, hac, refl⟩
  | @tail d e _ hde ih =>
    rcases ih with ⟨b, hdb, hcb⟩
    have : ∃ a, ReflTransGen r e a ∧ ReflGen r b a := by
      clear hcb
      induction hdb with
      | refl => exact ⟨e, refl, ReflGen.single hde⟩
      | @tail f b _ hfb ih =>
        rcases ih with ⟨a, hea, hfa⟩
        cases hfa with
        | refl => exact ⟨b, hea.tail hfb, ReflGen.refl⟩
        | single hfa =>
          spytial f
          rcases h _ _ _ hfb hfa with ⟨c, hbc, hac⟩
          spytial f
          exact ⟨c, hea.trans hac, hbc⟩
    rcases this with ⟨a, hea, hba⟩
    cases hba with
    | refl => exact ⟨b, hea, hcb⟩
    | single hba => exact ⟨a, hea, hcb.tail hba⟩

namespace Counterexample

inductive State where
  | a | b | x | y
  deriving DecidableEq

inductive Step : State → State → Prop where
  | ab : Step .a .b
  | ba : Step .b .a
  | ax : Step .a .x
  | by : Step .b .y

theorem locally_confluent (s t u : State) (hst : Step s t) (hsu : Step s u) :
    Join (ReflTransGen Step) t u := by
  cases hst <;> cases hsu
  all_goals first
    | exact ⟨_, .refl, .refl⟩
    | exact ⟨.x, (ReflTransGen.single Step.ba).tail Step.ax, .refl⟩
    | exact ⟨.x, .refl, (ReflTransGen.single Step.ba).tail Step.ax⟩
    | exact ⟨.y, (ReflTransGen.single Step.ab).tail Step.by, .refl⟩
    | exact ⟨.y, .refl, (ReflTransGen.single Step.ab).tail Step.by⟩

theorem x_terminal {z : State} (hxz : ReflTransGen Step .x z) : z = .x :=
  (reflTransGen_iff_eq (by intro t h; cases h)).mp hxz

theorem y_terminal {z : State} (hyz : ReflTransGen Step .y z) : z = .y :=
  (reflTransGen_iff_eq (by intro t h; cases h)).mp hyz

theorem sinks_not_joinable : ¬ Join (ReflTransGen Step) State.x State.y := by
  rintro ⟨z, hxz, hyz⟩
  cases (x_terminal hxz).symm.trans (y_terminal hyz)

theorem not_confluent :
    ¬ (∀ s t u, ReflTransGen Step s t → ReflTransGen Step s u →
      Join (ReflTransGen Step) t u) := by
  intro h
  exact sinks_not_joinable (h .a .x .y (.single .ax) ((ReflTransGen.single Step.ab).tail Step.by))

theorem not_short_join :
    ¬ (∀ s t u, Step s t → Step s u → ∃ v, ReflGen Step t v ∧ ReflTransGen Step u v) := by
  intro h
  obtain ⟨v, hbv, hxv⟩ := h .a .b .x .ab .ax
  have hv := x_terminal hxv
  subst v
  cases hbv with
  | single hbx => cases hbx

end Counterexample
end ZulipConfluence
