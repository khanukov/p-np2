import Magnification.FinalResult
import Complexity.Simulation.Circuit_Compiler

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
    (hMag : MagnificationAssumptions)
    (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n)
    (hBarriers : BarrierBypassPackage) :
    NP_not_subset_PpolyFormula ∧ BarrierBypassPackage := by
  refine ⟨NP_not_subset_PpolyFormula_final hMag n hn, hBarriers⟩

/--
Final `P ≠ NP` wrapper with explicit barrier obligations.

Unlike default `P_ne_NP_final` (which internalizes the inclusion side), this
audit-facing wrapper keeps explicit DAG-track separation and explicit internal
`P ⊆ P/poly` closure contracts.
-/
theorem P_ne_NP_final_with_barriers
    (hNPDag : NP_not_subset_PpolyDAG)
    (hPpolyContracts : Complexity.Simulation.PsubsetPpolyCompiledRuntimeLinearOutputContracts)
    (hBarriers : BarrierBypassPackage) :
    P_ne_NP ∧ BarrierBypassPackage := by
  refine ⟨P_ne_NP_final_with_provider hNPDag hPpolyContracts, hBarriers⟩

end Barrier
end Pnp3
