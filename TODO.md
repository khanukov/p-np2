# To-Do
> **Status (2025-08-06)**: Tasks below track incomplete proofs and axioms.


Updated development tasks after audit (2025-08-06).

- [x] Complete proofs in `Pnp2/Cover/BuildCover.lean` (`buildCover_covers`).
- [ ] Optional: provide a constructive variant of `firstUncovered` in
      `Pnp2/Cover/Uncovered.lean`.
      * The existing classical search is perfectly acceptable for the Prop-level
        results proved in this project: we freely use `Classical.choice`,
        `funext`, `propext`, and `noncomputable` sections.  A constructive
        rewrite is tracked only for future executable tooling.
- [x] Provide a formal proof of `sunflower_exists_classic` in `Pnp2/Sunflower/Sunflower.lean`.
      * Proof completed; the classical sunflower lemma is now fully formalised.
 - [x] Replace provisional assumption `buildCover_card_le_pow2` and adjust
       `buildCover_card`/`buildCover_card_bigO` once the recursive cover algorithm is implemented.
- [x] Implement `decisionTree_cover` for low-sensitivity families.
      * Подробный план: см. `docs/decisionTree_cover_plan.md`.
      * The large-sensitivity branch reuses `buildCover`, while the fallback
        simply enumerates singleton subcubes, so no unfinished permutation
        lemmas or auxiliary `sorry`s remain in this area.
- [ ] Replace complexity-theoretic assumptions in `Pnp2/NP_separation.lean` with proven results.
- [ ] Prove inclusion `P ⊆ P/poly` in `Pnp2/ComplexityClasses.lean`.

## Remaining axioms (as of 2025-08-06)

- `ComplexityClasses.P_subset_Ppoly`
- `NPSeparation.magnification_AC0_MCSP`
- `NPSeparation.karp_lipton`
- `NPSeparation.FCE_implies_MCSP`

## Outstanding `sorry`s (as of 2025-08-06)

- None – all previously unfinished decision-tree lemmas were removed or
  replaced by the singleton fallback argument.
