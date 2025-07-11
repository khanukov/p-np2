# To-Do

Short list of development tasks reflecting the current repository status.

- [x] Prove `exists_coord_card_drop` to complement the entropy-drop lemma.
- [ ] Move all modules from `Pnp2` into the `pnp` directory and add extensive
      tests for the migrated code.
- [ ] Complete `buildCover` proofs (the bound `mBound_lt_subexp` is now proven).
- [ ] Replace axioms `buildCover_mono` and `buildCover_card_bound` with full proofs.
- [ ] Integrate the decision-tree implementation with `low_sensitivity_cover`.
- [ ] Expand numeric bounds in `bound.lean`.
- [x] Provide more decision-tree utilities (leaf subcubes, path handling).
- [x] Formalise path length bounds like `path_to_leaf_length_le_depth`.
- [x] Prove basic leaf-count bound `leaf_count_le_pow_depth`.
- [x] Remove outdated sunflower branch placeholder in `Boolcube.buildCover`.
- [x] Drop obsolete note about `sorry` usage in `Boolcube.lean`.
- [x] Add `AllOnesCovered.union` helper lemma to simplify coverage proofs.
- [ ] Use `collentropy.lean` and `family_entropy_cover.lean` across modules.
- [x] Remove outdated standalone file `src/entropy_drop.lean` (lemma now lives in `Boolcube.lean`).
