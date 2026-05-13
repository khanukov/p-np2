/-!
# Smoke probe — rejected_phantom_axiom

Research Governance v0.1, PR 5.

This file intentionally introduces an `axiom P_ne_NP_unconditional`
declaration.  It is staged into
`pnp3/Tests/_smoke_probe_phantom_axiom.lean` by
`scripts/run_smoke_probes.sh`, the PR 1 guard
(`scripts/check_doc_honesty.sh` Part A) is run, and the file is then
removed.

This file is NOT part of `lake build`.
-/

namespace Pnp3

axiom P_ne_NP_unconditional : Pnp3.ComplexityInterfaces.P_ne_NP

end Pnp3
