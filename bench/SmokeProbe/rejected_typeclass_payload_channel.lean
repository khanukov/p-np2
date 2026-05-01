/-!
# Smoke probe — rejected_typeclass_payload_channel

Research Governance v0.1, PR 5.

This file intentionally uses the quarantined typeclass-payload channel
`[VacuousFinalPayloadProvider]` as a theorem parameter outside the
audit/test/docs zone.  It is staged into
`pnp3/Magnification/_smoke_probe_typeclass.lean` by
`scripts/run_smoke_probes.sh`, the PR 2 guard
(`scripts/check_typeclass_payload_quarantine.sh`) is run, and the
file is then removed.

This file is NOT part of `lake build`.
-/

namespace Pnp3
namespace Magnification

example [VacuousFinalPayloadProvider] :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  Vacuous_P_ne_NP_via_FinalPayloadProvider

end Magnification
end Pnp3
