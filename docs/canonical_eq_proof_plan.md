# Plan for the canonical equality theorem

This document sketches a proof of the statement
`canonical c₁ = canonical c₂ ↔ ∀ x, eval c₁ x = eval c₂ x` for Boolean circuits.
The outline follows two main steps.

1. **Soundness.**  If two circuits have the same canonical form then they
   are extensionally equal.  This direction is already formalised in the
   lemma `canonical_inj` from `canonical_circuit.lean` and relies on the
   correctness theorem `eval_canonical`.
2. **Completeness.**  Conversely, if the evaluations coincide on every
   input then the canonical forms must agree.  The intended proof proceeds
   by induction on the structure of the canonical circuits, analysing all
   constructor cases and showing that unequal canonical forms always yield
   a distinguishing input.  The long Russian note from the discussion
   expands this argument in detail, covering variables, constants, unary
   and binary gates and the corresponding inductive step.

Combining these directions establishes the desired equivalence, denoted
here as `canonical_eq_iff_eqv`.  The proof is not yet fully formalised in
Lean but the outline provides a concrete roadmap for completing the
implementation without disrupting existing tests.
