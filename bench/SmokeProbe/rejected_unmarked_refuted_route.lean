/-!
# Smoke probe — rejected_unmarked_refuted_route

Research Governance v0.1, PR 5.

This file intentionally declares a final-looking theorem under one of
the refuted-route suffix patterns (`_final_of_supportBounds`) without
the required `RefutedRoute_*` / `Vacuous_*` / `AuditOnly_*` prefix.
It is staged into
`pnp3/LowerBounds/_smoke_probe_unmarked_route.lean` by
`scripts/run_smoke_probes.sh`, the PR 3 guard
(`scripts/check_refuted_route_quarantine.sh`) is run, and the file
is then removed.

This file is NOT part of `lake build`.
-/

namespace Pnp3
namespace LowerBounds

theorem P_ne_NP_final_of_supportBounds (h : True) :
    Pnp3.ComplexityInterfaces.P_ne_NP := by
  exact (False.elim (by trivial : False))

end LowerBounds
end Pnp3
