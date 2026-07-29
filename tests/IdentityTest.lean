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
