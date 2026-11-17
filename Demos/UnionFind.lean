import SpytialLean

/-!
# Union-find

Each vertex has one parent. A root is its own parent. To find a representative, follow
parents until one points back to itself. To unite two sets, change the parent of the
first root to the second root.

Why update the root? If the roots differ and `x` lies below its root, redirecting `x`
would leave its old root and any other branches behind.

![The two searches before and after linking their roots](figures/union-roots.png)
-/

namespace UnionFindDemo

variable {α : Type u}

/-- Zero or more parent steps. A vertex can reach itself in zero steps. -/
inductive Reaches (parent : α → α) : α → α → Prop where
  | refl (x) : Reaches parent x x
  | step {x next root} : parent x = next → Reaches parent next root → Reaches parent x root

/-- Extend a path by one parent step at its endpoint. -/
theorem Reaches.append_step {parent : α → α} {x r s : α}
    (path : Reaches parent x r) (edge : parent r = s) : Reaches parent x s := by
  induction path with
  | refl => exact .step edge (.refl s)
  | step first _ ih => exact .step first (ih edge)

variable [DecidableEq α]

/-- Redirect one pointer. -/
def link (parent : α → α) (x root : α) : α → α :=
  fun v => if v = x then root else parent v

/-- Check at most `fuel` vertices for a self-parent. -/
def find? (parent : α → α) : Nat → α → Option α
  | 0, _ => none
  | fuel + 1, x => if parent x = x then some x else find? parent fuel (parent x)

/-- Link the first root to the second, only if both lookups succeed. -/
def union? (parent : α → α) (fuel : Nat) (x y : α) : Option (α → α) := do
  let rx ← find? parent fuel x
  let ry ← find? parent fuel y
  return link parent rx ry

/-- A successful search returns a root reachable from its starting vertex. -/
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
      obtain ⟨path, isRoot⟩ := ih (parent x) rest
      exact ⟨.step rfl path, isRoot⟩

/-- Redirecting a root preserves every old path. Any step out of the old root was a self-loop
and can be skipped. -/
theorem Reaches.link_of_root {parent : α → α} {x r old : α}
    (path : Reaches parent x r) (isRoot : parent old = old) (target : α) :
    Reaches (link parent old target) x r := by
  induction path with
  | refl => exact .refl _
  | @step v next _ edge _ ih =>
    by_cases h : v = old
    · subst v
      simpa only [← edge, isRoot] using ih
    · exact .step (by simpa [link, h] using edge) ih

/-- If the searches from `x` and `y` return `rx` and `ry`, union returns the map on the right.

```text
Before the link              After the link

x ~~> rx --> rx              x ~~> rx --+
                                        |
                                        v
y ~~> ry --> ry              y ~~~~~~~> ry --> ry

  -->  one parent pointer
  ~~>  zero or more parent pointers
```

Both vertices now reach `ry`, which is still its own parent. The roots may already coincide. -/
theorem union_roots (parent : α → α) (fuel : Nat) (x y rx ry : α)
    (hx : find? parent fuel x = some rx) (hy : find? parent fuel y = some ry) :
    union? parent fuel x y = some (link parent rx ry) ∧
      Reaches (link parent rx ry) x ry ∧ Reaches (link parent rx ry) y ry ∧
      link parent rx ry ry = ry := by
  obtain ⟨pathX, rootX⟩ := find?_sound parent fuel x rx hx
  obtain ⟨pathY, rootY⟩ := find?_sound parent fuel y ry hy
  spytial_spec α [hideAtom univ - α]
  -- A dashed edge records a proved path, even if its intermediate vertices are unknown.
  spytial x observing [parent, Reaches parent] with [..,
    edgeStyle «Reaches parent» (lineStyle dashed),
    hideField «Reaches parent» filter: (iden + parent),
    orientation «Reaches parent» - iden above
  ] titled "Before the link"

  let joined := link parent rx ry
  have xToRx : Reaches joined x rx := pathX.link_of_root rootX ry
  have yToRy : Reaches joined y ry := pathY.link_of_root rootX ry

  have newEdge : joined rx = ry := by simp [joined, link]
  have ryIsRoot : joined ry = ry := by simp [joined, link, rootY]
  -- In the joined map the old x-to-rx path can take the new parent step to ry.
  spytial x observing [joined, Reaches joined] fyi [Reaches.append_step (parent := joined)]
    nvm [rootX, rootY] with [..,
      edgeStyle «Reaches joined» (lineStyle dashed),
      hideField «Reaches joined» filter: (iden + joined),
      orientation «Reaches joined» - iden above
    ] titled "After the link"

  have xToRy := xToRx.append_step newEdge
  exact ⟨by simp [union?, hx, hy], xToRy, yToRy, ryIsRoot⟩

end UnionFindDemo
