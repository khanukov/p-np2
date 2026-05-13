/-!
# Smoke probe — rejected_bare_package_final

Research Governance v0.1, PR 5.

This file intentionally re-introduces a bare package-based final
endpoint name (`NP_not_subset_PpolyFormula_final`) without the
`RefutedRoute_` prefix that PR 3b mandates.  It is staged into
`pnp3/LowerBounds/_smoke_probe_bare_final.lean` by
`scripts/run_smoke_probes.sh`, the PR 3b extension of
`scripts/check_refuted_route_quarantine.sh` is run, and the file is
then removed.

This file is NOT part of `lake build`.
-/

namespace Pnp3
namespace LowerBounds

theorem NP_not_subset_PpolyFormula_final (h : True) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyFormula := by
  exact (False.elim (by trivial : False))

end LowerBounds
end Pnp3
