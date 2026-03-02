import Complexity.Simulation.Circuit_Compiler

namespace Pnp3.Tests

open Pnp3.Complexity

-- Default contract bundle must remain runtime-only.
example :
    Simulation.PsubsetPpolyInternalContracts ↔
      Simulation.InternalCompiler.RuntimeSpecProvider := Iff.rfl

-- Default closure theorem should not consume EvalAgreement/RuntimeConfigEqStepCompiled.
#check
  (Simulation.proved_P_subset_PpolyDAG_of_contracts :
    Simulation.PsubsetPpolyInternalContracts →
      ComplexityInterfaces.P_subset_PpolyDAG)

-- Compiled-runtime route is reduced to the minimal residual contract surface.
#check
  (Simulation.P_subset_PpolyDAG_of_compiledRuntimeContracts :
    Simulation.CompiledAcceptCircuitEvalAgreement →
      Simulation.CompiledAcceptCircuitSizeBound →
        ComplexityInterfaces.P_subset_PpolyDAG)

#check
  (Simulation.compiledAcceptEvalAgreement_of_outputWireAgreement :
    Simulation.CompiledAcceptOutputWireAgreement →
      Simulation.CompiledAcceptCircuitEvalAgreement)

#check
  (Simulation.compiledAcceptSizeBound_of_runtimeCircuitSizeBound :
    Simulation.CompiledRuntimeCircuitSizeBound →
      Simulation.CompiledAcceptCircuitSizeBound)

#check
  (Simulation.proved_P_subset_PpolyDAG_of_compiledRuntimeContracts :
    Simulation.PsubsetPpolyCompiledRuntimeContracts →
      ComplexityInterfaces.P_subset_PpolyDAG)

#check
  (Simulation.proved_P_subset_PpolyDAG_of_compiledRuntimeOutputAndSize :
    Simulation.CompiledAcceptOutputWireAgreement →
      Simulation.CompiledRuntimeCircuitSizeBound →
        ComplexityInterfaces.P_subset_PpolyDAG)

#check
  (Simulation.proved_P_subset_PpolyDAG_of_compiledRuntimeWireAndSize :
    Simulation.CompiledRuntimeWireEvalAgreement →
      Simulation.CompiledRuntimeCircuitSizeBound →
        ComplexityInterfaces.P_subset_PpolyDAG)

#check
  (Simulation.proved_P_subset_PpolyDAG_of_iteratedRuntimeOnlyContracts :
    Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly →
      ComplexityInterfaces.P_subset_PpolyDAG)

example :
    Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly ↔
      (Simulation.CompiledAcceptOutputWireAgreement ∧
        Simulation.CompiledRuntimeCircuitSizeBound) := by
  simp [Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly]

end Pnp3.Tests
