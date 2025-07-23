# Migration progress from `pnp` to `Pnp2`

Development has shifted back to the historical `Pnp2` namespace.  The `pnp`
folder remains in the repository only for reference.  Each module is being
ported across so that the proofs live under `Pnp2` once more.  The build still
includes the old code, but new lemmas and theorems appear only in `Pnp2`.

## Modules already migrated to `Pnp2`

- `BoolFunc.lean` and the `BoolFunc/` subdirectory
- `DecisionTree.lean`
- `Agreement.lean`
- `Boolcube.lean`
- `Collentropy.lean`
- `Entropy.lean`
- `Low_sensitivity_cover.lean`
- `Cover.lean`
- `Bound.lean`
- `ComplexityClasses.lean`
- `NP_separation.lean`
- `Acc_mcsp_sat.lean`
- `Canonical_circuit.lean`
- `Family_entropy_cover.lean`
- `Sunflower/` containing `RSpread.lean` and the ported proof `Sunflower.lean`
- `Cover_numeric.lean`
- `Examples.lean`
- `Low_sensitivity.lean`
- `Merge_low_sens.lean`
- `Table_locality.lean`
- `Pnp2.lean` as the root module

## Remaining work

All major files have been migrated to `Pnp2` and the legacy directory now
serves purely for historical reference.  Future clean-up will remove the
old tree once downstream tools no longer rely on it.
