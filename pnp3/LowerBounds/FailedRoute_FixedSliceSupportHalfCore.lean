import LowerBounds.RouteBSourceClosure

namespace Pnp3
namespace LowerBounds

open ComplexityInterfaces
open Models

/-!
Core impossibility payload for the historical fixed-slice support-half route.

This module keeps only the two structural incompatibility lemmas.
Higher-level restatements and user-facing corollaries are layered in
`FailedRoute_FixedSliceSupportHalfImpossible`.
-/

/--
If the fixed-slice language is already in `PpolyDAG`, then the stable-restriction
producer cannot hold.
-/
theorem no_fixedSlice_stableRestriction_of_inPpolyDAG
    {p : GapPartialMCSPParams}
    (hIn : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    ¬ dag_stableRestriction_producer p := by
  intro hStable
  exact (not_ppolyDAG_of_dag_stableRestriction (p := p) hStable) hIn

/--
Under fixed-slice `PpolyDAG` membership, the Route-B source blocker is impossible.
-/
theorem no_fixedSlice_blocker_of_inPpolyDAG
    {p : GapPartialMCSPParams}
    (hIn : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    ¬ dagRouteBSourceBlocker p := by
  intro hBlocker
  exact no_fixedSlice_stableRestriction_of_inPpolyDAG (p := p) hIn
    (dag_stableRestriction_producer_of_sourceClosure
      (dagRouteBSourceClosure_of_blocker (p := p) hBlocker))

end LowerBounds
end Pnp3
