import CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations.Refinement
import CLRSLean.FourthEdition.Chapter_19.Section_19_3_Disjoint_Set_Forests
import CLRSLean.FourthEdition.Chapter_20.Section_20_2_BFS

/-! Small executable checks and trust checks against the unmodified upstream declarations. -/

namespace CLRSCompatibility

open CLRS.Chapter13

def before : RBTree := .node .red .empty 1 (.node .red .empty 2 .empty)
def after : RBTree := .node .red (.node .red .empty 1 .empty) 2 .empty

#guard RBTree.rotateLeft before = after
#guard RBTree.keys before = [1, 2]
#guard RBTree.keys after = [1, 2]

def forest := CLRS.Chapter21.Forest.singletonForest 4
def joined := forest.union ⟨0, by decide⟩ ⟨1, by decide⟩

theorem joined_size : joined.size = 4 :=
  (CLRS.Chapter21.Forest.union_size forest ⟨0, by decide⟩ ⟨1, by decide⟩).trans
    (CLRS.Chapter21.Forest.singletonForest_size 4)

#guard forest.size = 4
#guard joined.size = 4
#guard (joined.checkEquiv
  ⟨0, by rw [joined_size]; decide⟩ ⟨1, by rw [joined_size]; decide⟩).2 = true
#guard (joined.checkEquiv
  ⟨0, by rw [joined_size]; decide⟩ ⟨2, by rw [joined_size]; decide⟩).2 = false

#print axioms RBTree.redBlackShape_repaint_rotateLeft_red_red
#print axioms CLRS.Chapter21.Forest.find_preserves_sameSet
#print axioms CLRS.Chapter21.Forest.union_sameSet_iff
#print axioms CLRS.Chapter22.Graph.bfsState_correct

end CLRSCompatibility
