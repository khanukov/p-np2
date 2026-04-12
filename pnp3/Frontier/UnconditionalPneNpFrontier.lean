import Magnification.FinalResultCore

namespace Pnp3
namespace Frontier

open Models
open LowerBounds
open Magnification
open ComplexityInterfaces

/-!
# Single-file frontier reduction (honest fallback)

This file intentionally concentrates the remaining DAG-side theorem debt into
one named proposition `CoreFrontierObligation`.

Current blocker reduced here:
- we do **not** have a compiled concrete fixed slice `p* : GapPartialMCSPParams`
  together with a concrete `GapPartialMCSP_TMWitness p*` in this branch, so the
  direct zero-argument `_TM` route to unconditional `P ≠ NP` cannot be closed
  from existing objects alone;
- therefore we expose the shortest honest fallback frontier: one support-half
  source obligation on one asymptotic slice (packed together with the needed
  asymptotic assumptions package).

If `CoreFrontierObligation` is proved, this file derives
`ComplexityInterfaces.NP_not_subset_PpolyDAG` immediately via existing wrappers.
It also derives `ComplexityInterfaces.P_ne_NP` by the already-compiled DAG-only
final wrapper.
The **last external object** still missing for the direct zero-argument theorem
is a concrete fixed-slice witness package
`W : Models.GapPartialMCSP_TMWitness p*` (with concrete `p*`) suitable for the
existing `_TM` wrappers.
-/

/--
Canonical single remaining frontier obligation.

Contentful payload (support-half priority): provide one asymptotic magnification
package and one concrete asymptotic slice where the Route-B source blocker
holds.  Everything downstream is packaging/glue.
-/
def CoreFrontierObligation : Prop :=
  ∃ hMag : MagnificationAssumptions,
    ∃ n : Nat,
      ∃ hn : hMag.antiChecker.asymptotic.N0 ≤ n,
        gapPartialMCSP_supportHalfObligation
          (hMag.antiChecker.asymptotic.pAt n hn)

/-- Adapter: turn support-half obligation into the named Route-B blocker. -/
private theorem blocker_of_supportHalf
    {hMag : MagnificationAssumptions}
    {n : Nat}
    {hn : hMag.antiChecker.asymptotic.N0 ≤ n}
    (hSupportHalf :
      gapPartialMCSP_supportHalfObligation
        (hMag.antiChecker.asymptotic.pAt n hn)) :
    dagRouteBSourceBlocker (hMag.antiChecker.asymptotic.pAt n hn) := by
  exact hSupportHalf

/--
Single-file reduction: proving `CoreFrontierObligation` is enough to derive the
repository's DAG-side class separation target.
-/
theorem frontier_reduces_to_real_NP_not_subset_PpolyDAG :
    CoreFrontierObligation → ComplexityInterfaces.NP_not_subset_PpolyDAG := by
  intro hCore
  rcases hCore with ⟨hMag, n, hn, hSupportHalf⟩
  exact
    NP_not_subset_PpolyDAG_final_of_asymptotic_blocker
      (hMag := hMag)
      (n := n)
      (hn := hn)
      (hBlocker := blocker_of_supportHalf (hMag := hMag) (n := n) (hn := hn) hSupportHalf)

/--
Companion end-to-end reduction: the same single frontier obligation already
implies the repository-level `P ≠ NP` interface through the DAG-only final
wrapper.
-/
theorem frontier_reduces_to_real_P_ne_NP :
    CoreFrontierObligation → ComplexityInterfaces.P_ne_NP := by
  intro hCore
  exact P_ne_NP_final_dag_only
    (frontier_reduces_to_real_NP_not_subset_PpolyDAG hCore)

end Frontier
end Pnp3
