# Migration progress from Pnp2 to pnp

The project has mostly completed the move from the historical `Pnp2` namespace
to the new `pnp` directory.  Every file now has a counterpart under
`pnp/Pnp/` and compiles in the new namespace.  The old `Pnp2` directory
remains in the repository for reference because several modules were only
ported as skeletons.

## Modules now in `pnp/Pnp/`

- `BoolFunc.lean` together with the subdirectory `BoolFunc/` (`Support.lean`,
  `Sensitivity.lean`)
- `DecisionTree.lean`
- `Agreement.lean`
- `Boolcube.lean`
- `Collentropy.lean`
- `Entropy.lean`
- `LowSensitivityCover.lean`
- `Cover.lean`
- `Bound.lean`
- `ComplexityClasses.lean`
- `NPSeparation.lean`
- `AccMcspSat.lean`
- `CanonicalCircuit.lean`
- `FamilyEntropyCover.lean`
- `Sunflower/` containing `RSpread.lean` and `Sunflower.lean`
- `CoverNumeric.lean`
- `Examples.lean`
- `LowSensitivity.lean`
- `MergeLowSens.lean`
- `TableLocality.lean`
- `Pnp.lean` acting as the root module

## Outstanding work

The implementations from `Pnp2` still contain complete statements and proofs
that have been replaced by placeholders in `pnp`.  The following parts are
missing and should be ported:

- the proofs of `aux_growth` and `mBound_lt_subexp` in `Bound.lean`
- the full definition of `mergeLowSensitivityCover` in `MergeLowSens.lean`
- the `low_sensitivity_cover` construction and helper lemmas from
  `LowSensitivity.lean`
- the example-driven code in `Examples.lean`
- the SAT outline in `AccMcspSat.lean`
- the separation lemma `P_ne_NP_of_MCSP_bound` from `NPSeparation.lean`
- numeric cover bounds in `CoverNumeric.lean`
- tests exercising these modules

Once these proofs and tests have been migrated, the `Pnp2` directory can be
removed entirely.
