/-!
# Smoke probe — rejected_candidate_sorry

Research Governance v0.1, PR 15.2.

Stand-alone Lean file containing a `sorry` placeholder.  The kernel
elaboration succeeds (sorry is a warning, not an error), so a naive
exit-code check would pass; `scripts/check_candidate_kernel.sh`
catches it via the explicit "uses 'sorry'" warning grep.

Used by `scripts/run_smoke_probes.sh` in probe-mode:

    scripts/check_candidate_kernel.sh --probe <staging_path>

Expected exit non-zero with `status=sorry-admit`.

This file is NOT part of `lake build`.
-/

namespace Pnp3.Candidates.SmokeProbe.Sorry

theorem oops : True := by sorry

end Pnp3.Candidates.SmokeProbe.Sorry
