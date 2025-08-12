# To-Do
> **Status (2025-08-06)**: Tasks below track incomplete proofs and axioms.


Updated development tasks after audit (2025-08-06).

- [ ] Complete proofs in `Pnp2/Cover/BuildCover.lean` (`buildCover_covers`).
- [ ] Make `firstUncovered` constructive in `Pnp2/Cover/Uncovered.lean`.
- [x] Provide a formal proof of `sunflower_exists_classic` in `Pnp2/Sunflower/Sunflower.lean`.
      * Proof completed; the classical sunflower lemma is now fully formalised.
- [ ] Replace stub `buildCover_card` and update `buildCover_card_bigO` in `Pnp2/cover_numeric.lean`.
- [ ] Implement `decisionTree_cover` for low-sensitivity families.
      * Подробный план: см. `docs/decisionTree_cover_plan.md`.
- [ ] Replace complexity-theoretic assumptions in `Pnp2/NP_separation.lean` with proven results.
- [ ] Prove inclusion `P ⊆ P/poly` in `Pnp2/ComplexityClasses.lean`.

## Remaining axioms (as of 2025-08-06)

- `LowSensitivityCover.decisionTree_cover`
- `ComplexityClasses.P_subset_Ppoly`
- `NPSeparation.magnification_AC0_MCSP`
- `NPSeparation.karp_lipton`
- `NPSeparation.FCE_implies_MCSP`

These axioms represent major gaps in the current formalisation.
