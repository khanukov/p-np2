import Complexity.Simulation.Circuit_Compiler
import Magnification.FinalResult

namespace Pnp3.Tests

open Pnp3.Complexity
open Pnp3.Magnification

-- Runtime-only iterated final wrapper must stay free of RuntimeConfigEqStepCompiled.
#check
  (P_ne_NP_final_with_iteratedRuntimeOnlyProvider :
    ComplexityInterfaces.NP_not_subset_PpolyDAG →
      Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly →
        ComplexityInterfaces.P_ne_NP)

#check
  (P_ne_NP_final_with_iteratedProvider_internal :
    ComplexityInterfaces.NP_not_subset_PpolyDAG →
      Simulation.PsubsetPpolyInternalContractsIteratedCanonical →
        ComplexityInterfaces.P_ne_NP)

#check
  (P_ne_NP_final :
    ComplexityInterfaces.NP_not_subset_PpolyDAG →
      Simulation.PsubsetPpolyInternalContractsIteratedCanonical →
        ComplexityInterfaces.P_ne_NP)

example :
    Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly ↔
      (Simulation.CompiledAcceptOutputWireAgreement ∧
        Simulation.CompiledRuntimeCircuitSizeBound) := by
  simp [Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly]

example :
    Simulation.PsubsetPpolyInternalContractsIteratedCanonical ↔
      Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly := Iff.rfl

end Pnp3.Tests
