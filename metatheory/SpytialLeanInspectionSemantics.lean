module

public import SpytialLeanInspectionSemantics.Relational
public import SpytialLeanInspectionSemantics.Inspection
public import SpytialLeanInspectionSemantics.Correctness

/-!
# Relational inspection by computation and proof

This library explains the idea behind Spytial's relational inspection with a small Lean formalism.
It is not a correctness proof of the production relationalizer. Ordinary structural
relationalization enters only through the explicit `StructuralSound` premise, and the connection
between semantic atoms and Lean expressions is left abstract.

* `Relational` defines typed positive relational instances and their possible-world meaning.
* `Inspection` defines how a value is exposed by computation or proof and the inspection judgment.
* `Correctness` proves soundness and agreement between computation- and proof-exposed structure.
-/
