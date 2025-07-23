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

Several statements in the `pnp` tree still provide more complete proofs.
The following items need to be moved and checked:

- the proofs of `aux_growth` and `mBound_lt_subexp` in `bound.lean`
- the full definition of `mergeLowSensitivityCover` in `merge_low_sens.lean`
- the `low_sensitivity_cover` construction from `low_sensitivity.lean`
- the example-driven code in `examples.lean`
- the SAT outline in `acc_mcsp_sat.lean`
- the separation lemma `P_ne_NP_of_MCSP_bound` from `NP_separation.lean`
- numeric cover bounds in `cover_numeric.lean`
- tests exercising these modules

Once all modules are moved and the proofs re-established, the `pnp`
directory can be dropped entirely.
