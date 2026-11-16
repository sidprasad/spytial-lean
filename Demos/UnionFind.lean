import SpytialLean

/-!
# Union-find: which pointer does union change?

Two searches start at `x` and `y` and return `rx` and `ry`. Suppose the roots are
distinct and `x` lies below `rx`. Setting the parent of `x` to `y` would move the
branch under `x`. Even `rx` itself would stay behind. Which pointer moves the whole set?

Start at `union_roots` and follow the three `spytial x` calls. The first two observe
the same parent function on either side of a proof. The third observes the function
union will return. All four vertices are variables, and the roots may coincide.
-/

namespace UnionFindDemo

variable {α : Type u} [DecidableEq α]

/-- Zero or more parent steps. A vertex can reach itself in zero steps. -/
inductive Reaches (parent : α → α) : α → α → Prop where
  | refl (x) : Reaches parent x x
  | step {x next root} : parent x = next → Reaches parent next root → Reaches parent x root

/-- Redirect one pointer. -/
def link (parent : α → α) (x root : α) : α → α :=
  fun v => if v = x then root else parent v

def find? (parent : α → α) : Nat → α → Option α
  | 0, _ => none
  | fuel + 1, x => if parent x = x then some x else find? parent fuel (parent x)

/-- Link the first root to the second, only if both lookups succeed. -/
def union? (parent : α → α) (fuel : Nat) (x y : α) : Option (α → α) := do
  let rx ← find? parent fuel x
  let ry ← find? parent fuel y
  return link parent rx ry

/-! ## Reading the forest

In the Spytial-CLRS forest view, parent arrows point up and vertices at equal
depth share a row. Here the depth of `x` is unknown. A `found` arrow leads upward
to the search result in one drawn edge, however many parent steps the search took.

A self-loop identifies a vertex of known depth zero. The layout aligns these
roots using the map `p` we are inspecting. Passing `link` at the last call makes
the row depend on the updated map. [Spytial-CLRS disjoint sets](https://github.com/sidprasad/spytial-clrs/blob/1a1e5e044b797197dcdadcc722a93a0bf0a93829/src/disjoint-sets.ipynb)
-/

open SpytialLean in
set_option hygiene false in
local macro "forestView(" p:ident ")" : spytial_op =>
  `(spytial_op| [
    orientation ($p:ident + found) - iden above,
    align let roots = ($p:ident & iden).univ | (roots -> roots) - iden horizontal
  ])

/-- Each successful recursive call supplies a path from the next vertex to the root.
Prepending the first parent step gives a path from the original query. -/
theorem find?_sound (parent : α → α) (fuel : Nat) (x root : α)
    (found : find? parent fuel x = some root) :
    Reaches parent x root ∧ parent root = root := by
  induction fuel generalizing x with
  | zero => simp [find?] at found
  | succ fuel ih =>
    by_cases hx : parent x = x
    · have hxr : x = root := by simpa [find?, hx] using found
      subst root
      exact ⟨.refl x, hx⟩
    · have rest : find? parent fuel (parent x) = some root := by
        simpa [find?, hx] using found
      generalize edge : parent x = next at rest
      obtain ⟨path, isRoot⟩ := ih next rest
      exact ⟨.step edge path, isRoot⟩

theorem Reaches.link_target {parent : α → α} {x target : α}
    (path : Reaches parent x target) (root : α) :
    Reaches (link parent target root) x root := by
  induction path with
  | refl => exact .step (by simp [link]) (.refl root)
  | @step x next target edge _ ih =>
    by_cases hx : x = target
    · subst x
      exact .step (by simp [link]) (.refl root)
    · exact .step (by simpa [link, hx] using edge) ih

theorem Reaches.link_root {parent : α → α} {x root : α}
    (path : Reaches parent x root) (target : α) :
    Reaches (link parent target root) x root := by
  induction path with
  | refl => exact .refl _
  | @step x next root edge _ ih =>
    by_cases hx : x = target
    · subst x
      exact .step (by simp [link]) (.refl root)
    · exact .step (by simpa [link, hx] using edge) ih

theorem link_isRoot (parent : α → α) (target root : α) (hr : parent root = root) :
    link parent target root root = root := by
  simp [link, hr]

/-! ## Inspecting `x` during the proof

The goal names a new parent function, `link parent rx ry`. To justify this choice,
we need to know where the old paths end and what the new function does at those
endpoints. The proof never needs a list of the intermediate vertices.
-/

theorem union_roots (parent : α → α) (fuel : Nat) (x y rx ry : α)
    (hx : find? parent fuel x = some rx) (hy : find? parent fuel y = some ry) :
    union? parent fuel x y = some (link parent rx ry) ∧
      Reaches (link parent rx ry) x ry ∧ Reaches (link parent rx ry) y ry ∧
      link parent rx ry ry = ry := by
  -- Read “found v r” as “the search from v returned r.”
  let found (v r : α) := find? parent fuel v = some r
  change found x rx at hx
  change found y ry at hy
  -- Follow the two arrows out of x. The search returns rx, while parent x is
  -- still unknown. Even parent rx is open. What tells us the search stopped at a root?
  spytial x observing [parent] with [forestView(parent)]

  let reaches := Reaches parent
  obtain ⟨pathX, rootX⟩ : reaches x rx ∧ parent rx = rx := find?_sound parent fuel x rx hx
  obtain ⟨pathY, rootY⟩ : reaches y ry ∧ parent ry = ry := find?_sound parent fuel y ry hy
  -- Inspect the same x and the same map. Now rx and ry have self-loops and share
  -- a row. The reaches edge takes x to rx. Every path ending there can use the
  -- same new step from rx to ry, whatever its first step was.
  spytial x observing [parent] with [forestView(parent)]

  -- Follow link from rx to ry, then around ry's self-loop. At x the new parent
  -- is still conditional because x could itself be rx. The goal asks where x
  -- can reach, so the path proof can finish with that first step still open.
  spytial x observing [link parent rx ry] with [forestView(link)]
  exact ⟨by simp_all [union?, found], pathX.link_target ry,
    pathY.link_root rx, link_isRoot parent rx ry rootY⟩

end UnionFindDemo
