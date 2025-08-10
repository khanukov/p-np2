# To-Do
> **Status (2025-08-06)**: Tasks below track incomplete proofs and axioms.


Updated development tasks after audit (2025-08-06).

- [ ] Complete proofs in `Pnp2/Cover/BuildCover.lean` (`buildCover_covers`, `buildCover_card_bound`, `mu_buildCover_lt_start`).
- [ ] Prove `exists_restrict_half_real_aux` and remove dependent axioms in `Pnp2/entropy.lean`.
- [ ] Make `firstUncovered` constructive in `Pnp2/Cover/Uncovered.lean`.
- [ ] Provide a formal proof of `sunflower_exists` in `Pnp2/Sunflower/Sunflower.lean`.
- [ ] Replace stub `buildCover_card` and update `buildCover_card_bigO` in `Pnp2/cover_numeric.lean`.
- [ ] Implement `decisionTree_cover` for low-sensitivity families.
- [ ] Replace complexity-theoretic assumptions in `Pnp2/NP_separation.lean` with proven results.
- [ ] Prove inclusion `P ⊆ P/poly` in `Pnp2/ComplexityClasses.lean`.

## Remaining axioms (as of 2025-08-06)

- `Sunflower.sunflower_exists`
- `Entropy.exists_restrict_half_real_aux`
- `LowSensitivityCover.decisionTree_cover`
- `ComplexityClasses.P_subset_Ppoly`
- `NPSeparation.magnification_AC0_MCSP`
- `NPSeparation.karp_lipton`
- `NPSeparation.FCE_implies_MCSP`

These axioms represent major gaps in the current formalisation.
