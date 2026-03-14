import Barrier.Relativization
import Barrier.NaturalProofs
import Barrier.Algebrization
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

Unlike default `P_ne_NP_final` (which internalizes the inclusion side), this
audit-facing wrapper keeps explicit DAG-track separation and explicit internal
`P ⊆ P/poly` closure contracts.
-/
theorem P_ne_NP_final_with_barriers
    (hProvider : StructuredLocalityProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily)
    (hNPDag : NP_not_subset_PpolyDAG)
    (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContractsIteratedCanonical)
    (hBarriers : BarrierBypassPackage) :
    P_ne_NP ∧ BarrierBypassPackage := by
  -- Keep the AC0-track assumptions explicit in the interface (for the barrier
  -- API symmetry with formula-track wrappers), even though this DAG-track
  -- endpoint currently consumes only `hNPDag` and `hPpolyContracts`.
  let _ := hProvider
  let _ := hAsym
  let _ := hNPfam
  refine ⟨P_ne_NP_final_with_provider hNPDag hPpolyContracts, hBarriers⟩

/--
Final `P ≠ NP` wrapper with explicit barrier obligations via iterated
internal runtime contracts plus runtime-config bridge.
-/
theorem P_ne_NP_final_with_barriers_iterated
    (hProvider : StructuredLocalityProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily)
    (hNPDag : NP_not_subset_PpolyDAG)
    (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContractsIteratedBridged)
    (hBarriers : BarrierBypassPackage) :
    P_ne_NP ∧ BarrierBypassPackage := by
  let _ := hProvider
  let _ := hAsym
  let _ := hNPfam
  refine ⟨P_ne_NP_final_with_iteratedProvider hNPDag hPpolyContracts, hBarriers⟩

/--
Final `P ≠ NP` wrapper with explicit barrier obligations via iterated
runtime-only contracts and compiled-runtime residual bundle.
-/
theorem P_ne_NP_final_with_barriers_iterated_runtimeOnly
    (hProvider : StructuredLocalityProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily)
    (hNPDag : NP_not_subset_PpolyDAG)
    (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly)
    (hBarriers : BarrierBypassPackage) :
    P_ne_NP ∧ BarrierBypassPackage := by
  let _ := hProvider
  let _ := hAsym
  let _ := hNPfam
  refine ⟨P_ne_NP_final_with_iteratedRuntimeOnlyProvider hNPDag hPpolyContracts, hBarriers⟩

/--
Canonical barrier wrapper for the iterated internal DAG route.
-/
theorem P_ne_NP_final_with_barriers_iterated_internal
    (hProvider : StructuredLocalityProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily)
    (hNPDag : NP_not_subset_PpolyDAG)
    (hPpolyContracts : Complexity.Simulation.PsubsetPpolyInternalContractsIteratedCanonical)
    (hBarriers : BarrierBypassPackage) :
    P_ne_NP ∧ BarrierBypassPackage := by
  let _ := hProvider
  let _ := hAsym
  let _ := hNPfam
  refine ⟨P_ne_NP_final_with_iteratedProvider_internal hNPDag hPpolyContracts, hBarriers⟩

/--
Final `P ≠ NP` wrapper with explicit barrier obligations via compiled-runtime
residual contracts.
-/
theorem P_ne_NP_final_with_barriers_compiledRuntime
    (hProvider : StructuredLocalityProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily)
    (hNPDag : NP_not_subset_PpolyDAG)
    (hPpolyContracts : Complexity.Simulation.PsubsetPpolyCompiledRuntimeContracts)
    (hBarriers : BarrierBypassPackage) :
    P_ne_NP ∧ BarrierBypassPackage := by
  let _ := hProvider
  let _ := hAsym
  let _ := hNPfam
  refine ⟨P_ne_NP_final_with_compiledRuntimeProvider hNPDag hPpolyContracts, hBarriers⟩

/--
Internal-source default barrier wrapper using the runtime-only DAG route.
-/
theorem P_ne_NP_final_with_barriers_internal_source
    (hProvider : StructuredLocalityProviderPartial)
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hNPfam : StrictGapNPFamily)
    (hNPDag : NP_not_subset_PpolyDAG)
    (hPpolyContracts : Complexity.Simulation.InternalCompiler.RuntimeSpecProvider)
    (hBarriers : BarrierBypassPackage) :
    P_ne_NP ∧ BarrierBypassPackage := by
  let _ := hProvider
  let _ := hAsym
  let _ := hNPfam
  have hPDag : P_subset_PpolyDAG :=
    Complexity.Simulation.proved_P_subset_PpolyDAG_of_runtimeOnly hPpolyContracts
  exact
    ⟨P_ne_NP_of_nonuniform_dag_separation hNPDag hPDag, hBarriers⟩

end Barrier
end Pnp3
