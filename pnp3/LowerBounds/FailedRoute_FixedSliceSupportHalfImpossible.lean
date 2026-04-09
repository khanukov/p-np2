import LowerBounds.FailedRoute_FixedSliceSupportHalfCore

namespace Pnp3
namespace LowerBounds

open ComplexityInterfaces
open Models

/-!
This module stores user-facing restatements for a **closed historical route**:
fixed-slice support-half blockers under `PpolyDAG` membership assumptions.

These statements are intentionally separated from active Route-B closure
plumbing so that final endpoints depend only on live source interfaces.
-/

/--
Audit-facing restatement under the original support-half name.

This is the same mathematical statement as
`no_fixedSlice_blocker_of_inPpolyDAG`, because
`dagRouteBSourceBlocker` is currently an abbreviation for
`gapPartialMCSP_supportHalfObligation`.
-/
theorem not_gapPartialMCSP_supportHalfObligation_of_inPpolyDAG
    {p : GapPartialMCSPParams}
    (hIn : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    ¬ gapPartialMCSP_supportHalfObligation p := by
  simpa [dagRouteBSourceBlocker] using
    (no_fixedSlice_blocker_of_inPpolyDAG (p := p) hIn)

/--
Contrapositive audit helper: proving a support-half blocker on a fixed slice
forces `¬ PpolyDAG` for that fixed-slice language.

This theorem is intentionally phrased as an implication into non-membership,
because fixed-slice hardwiring arguments are usually easier to state as
membership assumptions and then combined with this lemma by contradiction.
-/
theorem gapPartialMCSP_supportHalfObligation_implies_not_PpolyDAG
    {p : GapPartialMCSPParams}
    (hSupportHalf : gapPartialMCSP_supportHalfObligation p) :
    ¬ ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) := by
  intro hIn
  exact (not_gapPartialMCSP_supportHalfObligation_of_inPpolyDAG
    (p := p) hIn) hSupportHalf

end LowerBounds
end Pnp3
