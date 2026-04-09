import LowerBounds.RouteBSourceClosure
import LowerBounds.FailedRoutes

namespace Pnp3
namespace LowerBounds

/-!
Compatibility aggregation module (legacy import surface).

This file intentionally re-exports:

1. `RouteBSourceClosure` (active Route-B source/closure interfaces),
2. `FailedRoutes` (aggregated closed-route modules, including fixed-slice
   support-half impossibility and `GapSliceFamily` vacuity facts).

The goal is to keep legacy imports stable while separating "active route
plumbing" from "closed/failed-route impossibility facts" into explicitly named
modules.
-/

end LowerBounds
end Pnp3
