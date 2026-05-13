/-!
# Smoke probe — rejected_imports_refuted

Research Governance v0.1, PR 5.

This file intentionally references a refuted predicate from a hard-fail
zone (`pnp3/Complexity/`).  It is staged into
`pnp3/Complexity/_smoke_probe_imports_refuted.lean` by
`scripts/run_smoke_probes.sh`, the PR 4a guard
(`scripts/check_refuted_predicate_usage.sh`) is run, and the file is
then removed.

This file is NOT part of `lake build`; it is loaded by the smoke
driver only.  Do not import or compile it directly.
-/

namespace Pnp3
namespace Complexity

example (h : Magnification.FormulaSupportRestrictionBoundsPartial) :
    True := trivial

end Complexity
end Pnp3
