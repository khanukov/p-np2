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
- [ ] Implement `decisionTree_cover` for low-sensitivity families.
      * Подробный план: см. `docs/decisionTree_cover_plan.md`.
      * Current blockers: the lemma `exists_common_monochromatic_subcube` still
        contains two `sorry`s (global monochromaticity of the final cube and the
        codimension estimate), and the path-permutation lemmas in
        `DecisionTree.lean` (`coloredSubcubesAux_cons_bubble`,
        `coloredSubcubesAux_cons_subset_node_perm`, …) remain unfinished.
- [ ] Replace complexity-theoretic assumptions in `Pnp2/NP_separation.lean` with proven results.
- [ ] Prove inclusion `P ⊆ P/poly` in `Pnp2/ComplexityClasses.lean`.

## Remaining axioms (as of 2025-08-06)

- `ComplexityClasses.P_subset_Ppoly`
- `NPSeparation.magnification_AC0_MCSP`
- `NPSeparation.karp_lipton`
- `NPSeparation.FCE_implies_MCSP`

## Outstanding `sorry`s (as of 2025-08-06)

- `exists_common_monochromatic_subcube` in `low_sensitivity_cover.lean`
  (monochromaticity of the limit cube and the codimension bound).
- Path-manipulation lemmas in `DecisionTree.lean`, starting with
  `coloredSubcubesAux_cons_bubble` and the branch `coloredSubcubesAux_cons_subset_*`
  family.
