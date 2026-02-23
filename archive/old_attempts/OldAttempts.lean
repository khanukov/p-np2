import OldAttempts.BoolFunc.Sensitivity
import OldAttempts.DecisionTree
import OldAttempts.low_sensitivity_cover
import OldAttempts.Cover.Compute
-- import OldAttempts.cover  -- heavy cover construction (unused in tests)
import OldAttempts.Algorithms.SatCover

/-!
  Entrypoint for the legacy `old_attempts` toy development.
  This module merely re-exports the main definitions and lemmas used by
  the small test suite.  We keep it lightweight: any additional imports
  should only bring in minimal dependencies required for those tests.
-/
