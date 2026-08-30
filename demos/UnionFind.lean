import SpytialLean

open SpytialLean

/-! # Union-find: linking roots and shortening paths

Parent pointers are functions: sharing a parent means sharing a vertex, not copying a subtree.
A root points to itself. The concrete views below hide those self-edges and mark roots in green.

The proof-local inspection is in `Reaches.undo_link`, where a path uses the new shortcut. The
picture explains the next proof step: replace that edge with an old path and append the suffix
provided by the induction hypothesis. Dashed path edges stand for any number of parent steps;
they do not invent concrete intermediate vertices. The snapshots are just concrete context.

This is a small, unranked implementation. Lookup has a fuel bound and returns `none` on exhaustion
(including on a cycle), rather than pretending it found a root. Compression redirects just the
queried vertex to its root; it does not compress every intermediate vertex on the search path.
The proofs separate finding a root, linking components, and preserving a component by compression.
-/

namespace UnionFindDemo

variable {α : Type} [DecidableEq α]

/-- Change one parent pointer; all other pointers stay as they were. -/
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

/-- A single-vertex compression: bypass all intermediate parents of `x`. -/
def compress? (parent : α → α) (fuel : Nat) (x : α) : Option (α → α) := do
  let root ← find? parent fuel x
  return link parent x root

/-! ## Concrete states: which pointer changes?

There are initially three components: `a → b → c`, `d → e`, and the singleton `f`.
Union of `a` and `d` changes **only** `c`'s pointer to `e`, not `a`'s pointer to `d`.
Compressing `a` then changes **only** `a`'s pointer to `e`; `b → c → e` remains.
-/

inductive Vertex where
  | a | b | c | d | e | f
  deriving DecidableEq, SpytialIdentity

/-- A finite carrier lets the relationalizer tabulate the entire parent function. -/
structure Snapshot where
  parent : Vertex → Vertex

instance : SpytialIdentity Snapshot := .asWritten

spytial_spec Snapshot [
  inferredEdge pointer Snapshot.parent - iden,
  hideField parent,
  hideAtom Snapshot,
  orientation Snapshot.parent - iden above,
  align (Snapshot.parent - iden).~(Snapshot.parent - iden) horizontal,
  atomStyle {v : Vertex | v->v in Snapshot.parent}
    (borderStyle "#166534" 2) (fillStyle "#dcfce7")
]

def initial : Snapshot where
  parent
    | .a => .b
    | .b => .c
    | .c => .c
    | .d => .e
    | .e => .e
    | .f => .f

-- These witnesses make failed operations a compile error, not a fallback to the old state.
def joined : Snapshot := ⟨link initial.parent .c .e⟩

example : union? initial.parent 6 .a .d = some joined.parent := by rfl

def compressed : Snapshot := ⟨link joined.parent .a .e⟩

example : compress? joined.parent 6 .a = some compressed.parent := by rfl

-- Before union: c, e, and f are roots.
#spytial initial

-- After union: c now points to e; f is still a separate component.
#spytial joined

-- After compression: a goes straight to e; the other pointers do not move.
#spytial compressed

/-! ## Lookup: success is evidence of a path to a real root -/

inductive Reaches (parent : α → α) : α → α → Prop where
  | refl (x) : Reaches parent x x
  | step {x next root} : parent x = next → Reaches parent next root → Reaches parent x root

omit [DecidableEq α] in
theorem Reaches.trans {parent : α → α} {x y z : α}
    (hxy : Reaches parent x y) (hyz : Reaches parent y z) : Reaches parent x z := by
  induction hxy with
  | refl => exact hyz
  | step edge _ ih => exact .step edge (ih hyz)

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

/-! ## Union: redirect a root, not the queried vertex

Following a path to `target` after linking `target → root` leads on to `root`.
Paths that already ended at `root` still do so. These are different facts: together they explain
why both inputs belong to the merged component.
-/

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

theorem union_roots (parent : α → α) (fuel : Nat) (x y rx ry : α)
    (hx : find? parent fuel x = some rx) (hy : find? parent fuel y = some ry) :
    union? parent fuel x y = some (link parent rx ry) ∧
      Reaches (link parent rx ry) x ry ∧ Reaches (link parent rx ry) y ry ∧
      link parent rx ry ry = ry := by
  obtain ⟨pathX, _⟩ := find?_sound parent fuel x rx hx
  obtain ⟨pathY, rootY⟩ := find?_sound parent fuel y ry hy
  exact ⟨by simp [union?, hx, hy], pathX.link_target ry,
    pathY.link_root rx, link_isRoot parent rx ry rootY⟩

/-! ## Compression: the component stays the same

Every new edge is either an unchanged edge or the shortcut `target → root`. If that shortcut
already had an old path, any new path can be expanded back into old edges. Thus compression
preserves exactly the set of vertices that reach the chosen root; it does not merge components.
-/

theorem Reaches.undo_link {parent : α → α} {target root x y : α}
    (shortcut : Reaches parent target root) (path : Reaches (link parent target root) x y) :
    Reaches parent x y := by
  induction path with
  | refl => exact .refl _
  | @step x next y edge _ ih =>
    by_cases hx : x = target
    · subst x
      have he : root = next := by simpa [link] using edge
      cases he
      -- The path took the shortcut target → root. Why does it still exist in the old forest?
      -- Draw the orange single step next to the blue old paths: target ⇝ root (shortcut)
      -- and root ⇝ y (ih). Replacing the orange edge and concatenating gives the goal.
      -- Reaches has columns (parent map, start, end); select the old map from link's first
      -- column. The last two columns of link are the single step. The maps themselves are hidden.
      spytial target with [
        inferredEdge oldPath link.univ.univ.univ.univ.Reaches (lineStyle "#2563eb" dashed),
        inferredEdge shortcut univ.(univ.(univ.link)) (lineStyle "#d97706"),
        hideField Reaches,
        hideField link,
        hideAtom Reaches.univ.univ,
        orientation univ.Reaches - iden below,
        align univ.Reaches vertical
      ]
      exact shortcut.trans ih
    · exact .step (by simpa [link, hx] using edge) ih

theorem compression_component (parent : α → α) (fuel : Nat) (x root : α)
    (found : find? parent fuel x = some root) :
    compress? parent fuel x = some (link parent x root) ∧
      link parent x root root = root ∧
      ∀ v, Reaches (link parent x root) v root ↔ Reaches parent v root := by
  obtain ⟨path, isRoot⟩ := find?_sound parent fuel x root found
  refine ⟨by simp [compress?, found], link_isRoot parent x root isRoot, ?_⟩
  intro v
  exact ⟨fun h => Reaches.undo_link path h, fun h => h.link_root x⟩

/-! ## Boundary cases: unchanged partitions and unsuccessful searches -/

example : union? initial.parent 6 .a .b = some initial.parent := by
  change some (link initial.parent .c .c) = some initial.parent
  congr 1
  funext v
  cases v <;> rfl
example : compress? initial.parent 6 .c = some initial.parent := by
  change some (link initial.parent .c .c) = some initial.parent
  congr 1
  funext v
  cases v <;> rfl
example : find? initial.parent 0 .c = none := by decide
example : find? initial.parent 2 .a = none := by decide

def cyclicParent : Vertex → Vertex
  | .a => .b
  | .b => .a
  | v => v

example : find? cyclicParent 6 .a = none := by decide
example : union? cyclicParent 6 .a .f = none := by decide
example : compress? cyclicParent 6 .a = none := by decide

-- Check the data behind the concrete diagrams, including sharing and every unchanged pointer.
open Lean Meta in
#eval show MetaM Unit from do
  for (value, parents) in #[(``initial, #["b", "c", "c", "e", "e", "f"]),
      (``joined, #["b", "c", "e", "e", "e", "f"]),
      (``compressed, #["e", "c", "e", "e", "e", "f"])] do
    let data ← relationalize (mkConst value)
    unless (data.atoms.filter (·.type == "Vertex")).size == 6 do
      throwError "{value}: expected exactly six shared vertices"
    let some relation := data.relations.find? (·.name == "parent")
      | throwError "{value}: missing parent table"
    let label (id : String) := (data.atoms.find? (·.id == id)).map (·.label)
    let actual := relation.tuples.map fun tuple => (label tuple.atoms[1]!, label tuple.atoms[2]!)
    let expected := (#["a", "b", "c", "d", "e", "f"].zip parents).map fun (x, y) =>
      (some x, some y)
    unless actual == expected do
      throwError "{value}: parent graph drifted: {repr actual}"

end UnionFindDemo
