import Magnification.FinalResultMainline
import Magnification.FinalResultAuditRoutes
import Magnification.FinalResultWeakRoutes
import Magnification.FinalResultLegacyTM

namespace Pnp3
namespace Magnification

/-!
Compatibility aggregation module for the refactored final-result surface.

`FinalResultCore` re-exports four focused layers:

* `FinalResultMainline` — conditional integration surfaces and anti-checker /
  DAG mainline wrappers.  Active work should use its anti-checker-only DAG
  routes or the separate `UnconditionalResearchGap` boundary.

* `FinalResultAuditRoutes` — **audit / import-stability only.**  Every
  endpoint in this module carries an explicit `RefutedRoute_*` or
  `Vacuous_*` prefix (Research Constitution Rule 6): they consume refuted
  support-bounds / multi-switching / provider predicates and exist only so
  that legacy call sites and the falsifiability audit continue to compile.
  These are **not** claims; they must not be presented as the public closure
  boundary.

* `FinalResultWeakRoutes` — weak-route and bridge-local / class-level
  wrapper surface.  Conditional, not audit-only.

* `FinalResultLegacyTM` — `_TM` compatibility wrappers.  All endpoints
  carry `AuditOnly_*` (compatibility-only) or `RefutedRoute_*`
  (`_supportBounds_TM` companions) prefixes.

The active public closure boundary is in
`Magnification.UnconditionalResearchGap`:
`NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)` and
`P_ne_NP_final (gap : ResearchGapWitness)`.  Nothing in this aggregator
module replaces it.

Keeping this module thin preserves import stability for callers that
already use `Magnification.FinalResultCore`.
-/

end Magnification
end Pnp3
