import Magnification.FinalResultMainline
import Magnification.FinalResultWeakRoutes
import Magnification.FinalResultLegacyTM

namespace Pnp3
namespace Magnification

/-!
Compatibility aggregation module for the refactored final-result surface.

`FinalResultCore` now re-exports three focused layers:
- `FinalResultMainline`: conditional integration surfaces plus legacy/audit
  compatibility wrappers; active work should use its anti-checker-only DAG
  routes or the separate `UnconditionalResearchGap` boundary.
- `FinalResultWeakRoutes`: weak-route and bridge-local/class-level wrapper surface.
- `FinalResultLegacyTM`: stronger optional `_TM` compatibility wrappers and audit routes.

Keeping this module thin preserves import stability for callers that already
use `Magnification.FinalResultCore`.
-/

end Magnification
end Pnp3
