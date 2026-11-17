import Gillon

namespace GillonDemo

private def orderNat (a b : Nat) : Order :=
  if a < b then .LESS else if b < a then .GREATER else .EQUAL

private theorem less_iff (a b : Nat) : orderNat a b = .LESS ↔ a < b := by
  unfold orderNat
  split_ifs <;> simp_all

private theorem equal_iff (a b : Nat) : orderNat a b = .EQUAL ↔ a = b := by
  unfold orderNat
  split_ifs <;> simp_all <;> omega

private theorem greater_iff (a b : Nat) : orderNat a b = .GREATER ↔ b < a := by
  unfold orderNat
  split_ifs <;> simp_all
  omega

def natComparison : ComparisonFunction Nat where
  cmp := orderNat
  cmpEq := equal_iff
  cmpK := by simp [less_iff, equal_iff, greater_iff]
  cmpXor := by simp only [XOR3, less_iff, equal_iff, greater_iff]; omega
  cmpTransitiveLess := by simp only [less_iff]; omega
  cmpTransitiveGreater := by simp only [greater_iff]; omega
  cmpLessToGreater := by simp only [less_iff, greater_iff]; omega
  cmpGreaterToLess := by simp only [less_iff, greater_iff]; omega

private def fromKeys (keys : List Nat) : AVLTree Nat Nat natComparison :=
  keys.foldl (fun t k => t.insert k (10 * k)) (AVLTree.empty Nat Nat natComparison)

private def hasExpectedRoot (keys : List Nat) : Bool :=
  match (fromKeys keys).root with
  | .Node 2 2 20 (.Node 1 1 10 .Leaf .Leaf) (.Node 1 3 30 .Leaf .Leaf) => true
  | _ => false

-- Each of the four insertion paths must produce the same balanced map.
#guard hasExpectedRoot [3, 2, 1]
#guard hasExpectedRoot [3, 1, 2]
#guard hasExpectedRoot [1, 2, 3]
#guard hasExpectedRoot [1, 3, 2]
#guard (fromKeys []).lookup 2 == none
#guard (fromKeys [3, 1, 2]).lookup 4 == none
#guard ((fromKeys [3, 1, 2]).insert 1 99).lookup 1 == some 99
#guard ((fromKeys [3, 1, 2]).insert 1 99).lookup 3 == some 30

#print axioms AVLTree.insert
#print axioms AVLTree.AVLTreeInsertionProducesValue
#print axioms AVLTree.EmptyAVLTreeLookup

end GillonDemo
