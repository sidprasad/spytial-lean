module

public import SpytialLeanInspectionSemantics.Relational
public import SpytialLeanInspectionSemantics.Structural
public import SpytialLeanInspectionSemantics.Trace
public import SpytialLeanInspectionSemantics.Inspection
public import SpytialLeanInspectionSemantics.Correctness

/-!
# Relational inspection by computation and proof

This library explains the idea behind Spytial's relational inspection with a small Lean formalism.
It is not a correctness proof of the production relationalizer. The connection between semantic
atoms and Lean expressions is left abstract, and Lean's reduction is replaced by a small
operational semantics whose rules the model is assumed to validate.

* `Relational` defines typed positive relational instances and their possible-world meaning.
* `Structural` defines the core fragment's terms, their evaluation, the fixed meaning of generated
  field relations, and the recursive structural relationalizer.
* `Trace` tags every tuple with its origin, so a structural walk remembers whether evaluation or
  proof exposed the value it walked.
* `Inspection` defines exposure by evaluation or proof and the inspection judgment.
* `Correctness` proves soundness and agreement between evaluation- and proof-exposed structure.
-/
