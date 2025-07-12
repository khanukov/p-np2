# Migration progress from Pnp2 to pnp

The project is undergoing a gradual move from the historical `Pnp2` namespace to the new `pnp` directory. This file tracks which modules have already been transferred and which remain.

## Already migrated

The following modules now live under `pnp/Pnp/` and compile in the new
namespace:

- `BoolFunc.lean` together with the subdirectory `BoolFunc/` (including
  `Support.lean` and `Sensitivity.lean`).
- `DecisionTree.lean`.
- `Agreement.lean`.
- `Boolcube.lean`.
- `Collentropy.lean`.
- `Entropy.lean`.
- `LowSensitivityCover.lean`.
- `Pnp.lean` acting as the root module.

## Remaining to migrate

The following modules are still located under `Pnp2` and need to be copied into `pnp` while keeping the tests in sync:

 - `ComplexityClasses.lean`
 - `NP_separation.lean`
 - `Sunflower/RSpread.lean`
 - `acc_mcsp_sat.lean`
 - `bound.lean`
 - `canonical_circuit.lean`
 - `cover.lean`
 - `cover_numeric.lean`
 - `examples.lean`
 - `family_entropy_cover.lean`
 - `low_sensitivity.lean`
 - `merge_low_sens.lean`
 - `sunflower.lean`
 - `table_locality.lean`

Once all these files have been ported and compile successfully under the `pnp` namespace, the old `Pnp2` directory can be removed.
