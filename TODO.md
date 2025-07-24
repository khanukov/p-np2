# To-Do

Short list of development tasks reflecting the current repository status.

- [x] Prove `exists_coord_card_drop` to complement the entropy-drop lemma.
- [x] Move all modules from the legacy directory into `Pnp2` and add extensive
      tests for the migrated code.
- [x] Remove the `Pnp2` library from `lakefile.lean`; the directory is now kept
      only for reference.
- [x] Port missing proofs from `Pnp2` modules (Bound, LowSensitivity, MergeLowSens, CoverNumeric, NPSeparation, AccMcspSat) and add tests.
- [x] Port `Bound.mBound_lt_subexp` proof and related lemmas.
- [x] Complete `buildCover` proofs and establish the bound `mBound_lt_subexp`.
      The recursion on `μ(F, h, Rset) = 2 * h + |uncovered F Rset|` is now
      fully formalised and yields the lemma `buildCover_card_bound`.
* [x] Replace the axiom `buildCover_mono` with a complete proof.
  The counting lemma `buildCover_card_bound` is also fully proven using
  the measure recursion.
- [ ] Integrate the decision-tree implementation with `low_sensitivity_cover`.
- [ ] Expand numeric bounds in `bound.lean`.
- [x] Provide more decision-tree utilities (leaf subcubes, path handling).
- [x] Formalise path length bounds like `path_to_leaf_length_le_depth`.
- [x] Prove basic leaf-count bound `leaf_count_le_pow_depth`.
- [x] Show that every evaluation/path pair appears in `coloredSubcubes`.
- [x] Remove outdated sunflower branch placeholder in `Boolcube.buildCover`.
- [x] Drop obsolete note about `sorry` usage in `Boolcube.lean`.
- [x] Add `AllOnesCovered.union` helper lemma to simplify coverage proofs.
- [x] Integrate `sunflower_step` into `buildCover` and update the documentation.
- [ ] Use `collentropy.lean` and `family_entropy_cover.lean` across modules.
- [x] Remove outdated standalone file `src/entropy_drop.lean` (lemma now lives in `Boolcube.lean`).
- [ ] Complete the constructive cover enumerator in `Cover/Compute.lean` and prove
      `buildCoverCompute_spec`.
- [x] Prove `satViaCover_correct` and establish a time bound in
      `Algorithms/SatCover.lean`.

## Remaining axioms (as of 2025-07-16)
 - `LowSensitivityCover.decisionTree_cover` (external)
 - `ComplexityClasses.P_subset_Ppoly` (external)
 - `NPSeparation.MCSP_lower_bound` (external)
 - `NPSeparation.magnification_AC0_MCSP` (external)
 - `NPSeparation.PH_collapse` (external)
 - `NPSeparation.karp_lipton` (external)
 - `NPSeparation.FCE_implies_MCSP`

The complexity-theoretic axioms are expected to remain long‑term.
The numeric bounds and halving lemma will be replaced by actual proofs in future commits.
