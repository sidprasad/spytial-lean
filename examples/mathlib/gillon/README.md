# Gillon’s verified AVL map

[Open the literate Lean demo](Gillon.lean) inside the `examples/mathlib` Lake project. Start at `AVLTree.insertNode` and follow insertion back to the parent. Each of the six `spytial` calls has a short comment explaining what to inspect and which question it answers. The file contains the complete map and Gillon’s completed proofs. [Published source, Appendix A](https://www.andrew.cmu.edu/user/avigad/Students/gillon_landc_thesis.pdf#page=6)

For the inner-heavy case, open `AVLTree.rebalanceLeft`. The first inspection is in the proof that the inner child must contain a node. The second is the expression that builds the new root. The right-heavy implementation has the two mirror inspections. The single-rotation helpers each inspect their result as well. Select the function name in Lean’s infoview to compare its inspection sites. [Illustrated design experiment](../../../Demos/GillonAVL.md)

The observer `AVLNode.structuralHeight` is an alias for Gillon’s recursive `AVLNode.height`. His node constructor also has a *stored* field named `height`. Distinct relation names let the diagram keep the cache and the computed result apart. In a large proof context, the bounded simplifier can leave some observer applications symbolic. The type-level spec follows left and right children from the expression under the cursor. Keys appear on opened nodes and observed heights on the unopened fringe. Two subtrees with the same observed result align horizontally. The infoview’s context lists facts about the earlier tree as well.

## Reproduce from the appendix

From this directory, with Python 3, Ghostscript and `patch` installed, run

```sh
curl -fLsS https://www.andrew.cmu.edu/user/avigad/Students/gillon_landc_thesis.pdf -o /tmp/gillon-avl.pdf
python3 prepare.py /tmp/gillon-avl.pdf
cd ..
lake build Gillon
lake env lean gillon/Smoke.lean
```

Preparation reconstructs the Lean identifiers from the PDF glyph positions, then applies the checked-in patch for Lean and mathlib 4.33.1. From the Lake project, `diff -u gillon/Gillon.lean .lake/gillon/Gillon.lean` compares the reconstruction with the editable demo. Building and reading the demo need only the checked-in Lean source.

The port makes implicit result types explicit where current Lean needs them and updates tactics and lemma names. The originally unproved claim `AVLTreeInsertionDoesNotModifyOtherValues` is available as a proposition. Gillon’s proofs of lookup after inserting the requested key and lookup on the empty map are present as theorems. [Thesis §2.3](https://www.andrew.cmu.edu/user/avigad/Students/gillon_landc_thesis.pdf#page=4)

The smoke file checks one insertion sequence for each rotation, including the resulting shape, key/value positions and cached heights. It also checks overwrite and missing-key behavior, and prints the axiom dependencies of insertion and the two published lookup theorems. [Smoke checks](Smoke.lean)
