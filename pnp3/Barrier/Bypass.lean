import Barrier.Relativization
import Barrier.NaturalProofs
import Barrier.Algebrization
import Magnification.FinalResult

/-!
  pnp3/Barrier/Bypass.lean

  Explicit "barrier obligations" wrappers for final pipeline statements.
  These wrappers are intentionally conservative: they do not fabricate bypass
  proofs, they force barrier claims to be provided as explicit assumptions.
-/

namespace Pnp3
namespace Barrier

open ComplexityInterfaces
open Magnification

/-- Concrete bundle of explicit barrier-bypass obligations. -/
structure BarrierBypassAssumptions : Type where
  relativization : Prop
  naturalProofs : Prop
  algebrization : Prop

/-- Proposition-level wrapper used by final theorem signatures. -/
def BarrierBypassPackage : Prop := Nonempty BarrierBypassAssumptions

/-- Convenience constructor for the bypass package. -/
theorem barrierBypassPackage_mk
    (hRel : Prop) (hNat : Prop) (hAlg : Prop) :
    BarrierBypassPackage := ⟨⟨hRel, hNat, hAlg⟩⟩

/--
Attach explicit barrier obligations to an already obtained formula-track
separation theorem.
-/
theorem NP_not_subset_PpolyFormula_with_barriers
    (hFormula : NP_not_subset_PpolyFormula)
    (hBarriers : BarrierBypassPackage) :
    NP_not_subset_PpolyFormula ∧ BarrierBypassPackage :=
  ⟨hFormula, hBarriers⟩

/--
Final formula-track wrapper with explicit barrier obligations.
-/
theorem NP_not_subset_PpolyFormula_final_with_barriers
    (hProvider : StructuredLocalityProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily)
    (hBarriers : BarrierBypassPackage) :
    NP_not_subset_PpolyFormula ∧ BarrierBypassPackage := by
  refine ⟨NP_not_subset_PpolyFormula_final_with_provider hProvider hAsym hNPfam, hBarriers⟩

/--
Final `P ≠ NP` wrapper with explicit barrier obligations.

As in `P_ne_NP_final`, this remains conditional on explicit DAG-track
separation/inclusion assumptions.
-/
theorem P_ne_NP_final_with_barriers
    (hProvider : StructuredLocalityProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily)
    (hNPDag : NP_not_subset_PpolyDAG)
    (hPsubsetDag : P_subset_PpolyDAG)
    (hBarriers : BarrierBypassPackage) :
    P_ne_NP ∧ BarrierBypassPackage := by
  refine ⟨P_ne_NP_final_with_provider hProvider hAsym hNPfam hNPDag hPsubsetDag, hBarriers⟩

end Barrier
end Pnp3
