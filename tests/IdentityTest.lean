module

public meta import SpytialLean

open SpytialLean

/-! Golden tests for atom identity: when do two sub-values map to the same atom?
The goldens also lock atom ids and ordering, so identity changes that are meant
to be invisible (e.g. collision-proofing the memo) show up as a diff here. -/

namespace IdentityFixture

/-- Both components of the pair below are this one value: the walker must emit a
    single atom for it, referenced by both `fst` and `snd`. -/
public def sharedList : List Nat := [1, 2]

/-- Derived `BEq` is structural equality: two spellings of the same value
    (`2+2` vs `4` under a constructor) must collapse to one atom. -/
public inductive BTree where
  | nil
  | node (v : Nat) (l r : BTree)
  deriving BEq

public def bt1 : BTree := .node (2+2) .nil .nil
public def bt2 : BTree := .node 4 .nil .nil

/-- Hand-written `BEq` coarser than structure: declared equality is authoritative,
    so `⟨"A"⟩` and `⟨"a"⟩` collapse onto the *first* representative's atom. -/
public structure CI where
  s : String

public instance : BEq CI := ⟨fun a b => a.s.toLower == b.s.toLower⟩

/-- No instances at all: only syntactic sharing applies. `.leaf (0+1)` and `.leaf 1`
    stay two atoms (their whnf'd spellings differ) even though the values are equal —
    the deliberate conservative fallback. Their `Nat` child is still shared. -/
public inductive Plain where
  | leaf (n : Nat)
  | pair (a b : Plain)

end IdentityFixture

/--
info: {"relations":
 [{"types": ["Prod", "Prod"],
   "tuples": [{"types": ["Prod", "Prod"], "atoms": ["atom_0", "atom_1"]}],
   "name": "fst",
   "id": "fst"},
  {"types": ["Prod", "Prod"],
   "tuples": [{"types": ["Prod", "Prod"], "atoms": ["atom_0", "atom_1"]}],
   "name": "snd",
   "id": "snd"},
  {"types": ["List", "List"],
   "tuples":
   [{"types": ["List", "List"], "atoms": ["atom_1", "atom_2"]},
    {"types": ["List", "List"], "atoms": ["atom_3", "atom_4"]}],
   "name": "head",
   "id": "head"},
  {"types": ["List", "List"],
   "tuples":
   [{"types": ["List", "List"], "atoms": ["atom_3", "atom_5"]},
    {"types": ["List", "List"], "atoms": ["atom_1", "atom_3"]}],
   "name": "tail",
   "id": "tail"}],
 "atoms":
 [{"type": "Prod", "label": "mk", "id": "atom_0"},
  {"type": "List", "label": "cons", "id": "atom_1"},
  {"type": "Nat", "label": "1", "id": "atom_2"},
  {"type": "List", "label": "cons", "id": "atom_3"},
  {"type": "Nat", "label": "2", "id": "atom_4"},
  {"type": "List", "label": "nil", "id": "atom_5"}]}
-/
#guard_msgs in
#spytial.datum (IdentityFixture.sharedList, IdentityFixture.sharedList)

/--
info: {"relations":
 [{"types": ["BTree", "BTree"],
   "tuples": [{"types": ["BTree", "BTree"], "atoms": ["atom_1", "atom_3"]}],
   "name": "r",
   "id": "r"},
  {"types": ["Prod", "Prod"],
   "tuples": [{"types": ["Prod", "Prod"], "atoms": ["atom_0", "atom_1"]}],
   "name": "fst",
   "id": "fst"},
  {"types": ["BTree", "BTree"],
   "tuples": [{"types": ["BTree", "BTree"], "atoms": ["atom_1", "atom_2"]}],
   "name": "v",
   "id": "v"},
  {"types": ["BTree", "BTree"],
   "tuples": [{"types": ["BTree", "BTree"], "atoms": ["atom_1", "atom_3"]}],
   "name": "l",
   "id": "l"},
  {"types": ["Prod", "Prod"],
   "tuples": [{"types": ["Prod", "Prod"], "atoms": ["atom_0", "atom_1"]}],
   "name": "snd",
   "id": "snd"}],
 "atoms":
 [{"type": "Prod", "label": "mk", "id": "atom_0"},
  {"type": "BTree", "label": "node", "id": "atom_1"},
  {"type": "Nat", "label": "4", "id": "atom_2"},
  {"type": "BTree", "label": "nil", "id": "atom_3"}]}
-/
#guard_msgs in
#spytial.datum (IdentityFixture.bt1, IdentityFixture.bt2)

/--
info: {"relations":
 [{"types": ["Prod", "Prod"],
   "tuples": [{"types": ["Prod", "Prod"], "atoms": ["atom_0", "atom_1"]}],
   "name": "fst",
   "id": "fst"},
  {"types": ["CI", "CI"],
   "tuples": [{"types": ["CI", "CI"], "atoms": ["atom_1", "atom_2"]}],
   "name": "s",
   "id": "s"},
  {"types": ["Prod", "Prod"],
   "tuples": [{"types": ["Prod", "Prod"], "atoms": ["atom_0", "atom_1"]}],
   "name": "snd",
   "id": "snd"}],
 "atoms":
 [{"type": "Prod", "label": "mk", "id": "atom_0"},
  {"type": "CI", "label": "mk", "id": "atom_1"},
  {"type": "String", "label": "\"A\"", "id": "atom_2"}]}
-/
#guard_msgs in
#spytial.datum (IdentityFixture.CI.mk "A", IdentityFixture.CI.mk "a")

/--
info: {"relations":
 [{"types": ["Plain", "Plain"],
   "tuples":
   [{"types": ["Plain", "Plain"], "atoms": ["atom_1", "atom_2"]},
    {"types": ["Plain", "Plain"], "atoms": ["atom_3", "atom_2"]}],
   "name": "n",
   "id": "n"},
  {"types": ["Plain", "Plain"],
   "tuples": [{"types": ["Plain", "Plain"], "atoms": ["atom_0", "atom_1"]}],
   "name": "a",
   "id": "a"},
  {"types": ["Plain", "Plain"],
   "tuples": [{"types": ["Plain", "Plain"], "atoms": ["atom_0", "atom_3"]}],
   "name": "b",
   "id": "b"}],
 "atoms":
 [{"type": "Plain", "label": "pair", "id": "atom_0"},
  {"type": "Plain", "label": "leaf", "id": "atom_1"},
  {"type": "Nat", "label": "1", "id": "atom_2"},
  {"type": "Plain", "label": "leaf", "id": "atom_3"}]}
-/
#guard_msgs in
#spytial.datum (IdentityFixture.Plain.pair (.leaf (0+1)) (.leaf 1))
