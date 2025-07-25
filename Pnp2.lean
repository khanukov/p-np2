import Pnp2.BoolFunc.Sensitivity
import Pnp2.DecisionTree
import Pnp2.low_sensitivity_cover
import Pnp2.Cover.Compute
-- import Pnp2.cover  -- heavy cover construction (unused in tests)
import Pnp2.Algorithms.SatCover

/-!
  Entrypoint for the `pnp2` toy development.
  This module merely re-exports the main definitions and lemmas used by
  the small test suite.  We keep it lightweight: any additional imports
  should only bring in minimal dependencies required for those tests.
-/
