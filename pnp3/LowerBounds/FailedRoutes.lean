import LowerBounds.FailedRoute_FixedSliceSupportHalfCore
import LowerBounds.FailedRoute_FixedSliceSupportHalfImpossible
import LowerBounds.FailedRoute_GapSliceFamilyVacuous
import LowerBounds.FailedRoute_EventualTableForceSlackObstruction

namespace Pnp3
namespace LowerBounds

/-!
Aggregation module for closed / deprecated proof routes.

Purpose:
* give one import path for audit-only impossibility/vacuity facts,
* keep active endpoint modules free from historical-route statements,
* document that these imports are for diagnostics/audit only and must not be
  used as continuation targets for the main NP-vs-P/poly development.
-/

end LowerBounds
end Pnp3
