# To-Do
> **Status (2025-09-24)**: The combinatorial cover is fully formalised.  The items below track the remaining axioms and quality-of-life improvements.

## Complexity bridge

- [ ] Replace the axioms in `Pnp2/ComplexityClasses.lean` and `Pnp2/NP_separation.lean` with formal proofs:
  - Prove the classical circuit-simulation result `P ⊆ P/poly`.
  - Formalise the magnification link `magnification_AC0_MCSP` from ACC⁰ lower bounds to `NP ⊄ P/poly`.
  - Formalise the Karp–Lipton collapse (`karp_lipton`) and the bridge `FCE_implies_MCSP` from the constructive cover to the MCSP lower bound.

## Cover pipeline refinements (optional)

- [ ] Strengthen the coarse numeric bound in `Pnp2/cover_numeric.lean` (`buildCover_card = 2^n`) once sharper combinatorial estimates are available.
- [ ] Provide a constructive variant of `firstUncovered` in `Pnp2/Cover/Uncovered.lean` if executable tooling becomes a priority.  The current classical search is sufficient for the Prop-level results.

## Remaining axioms (as of 2025-09-24)

- `ComplexityClasses.P_subset_Ppoly`
- `NPSeparation.magnification_AC0_MCSP`
- `NPSeparation.karp_lipton`
- `NPSeparation.FCE_implies_MCSP`

## Outstanding `sorry`s (as of 2025-09-24)

- None – the Lean sources compile without placeholders.
