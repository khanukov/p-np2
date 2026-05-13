/-!
# Smoke probe — rejected_candidate_type_error

Research Governance v0.1, PR 15.2.

Stand-alone Lean file containing a type error.  Used by
`scripts/run_smoke_probes.sh` in probe-mode: the smoke driver stages
this file as a temporary path, then calls

    scripts/check_candidate_kernel.sh --probe <staging_path>

and asserts the script exits non-zero with `status=kernel-error`.

This file is NOT part of `lake build`; it lives only in
`bench/SmokeProbe/` and is loaded by the smoke driver on demand.
-/

namespace Pnp3.Candidates.SmokeProbe.TypeError

-- Deliberate type error: assigning a String literal to a Nat.
def broken : Nat := "this is a string, not a Nat"

end Pnp3.Candidates.SmokeProbe.TypeError
