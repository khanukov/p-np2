import Complexity.Simulation.Circuit_Compiler

namespace Pnp3.Tests

open Pnp3.Complexity

#check
  (Simulation.compiledAcceptEvalAgreementLinear_of_outputWireAgreement :
    Simulation.CompiledAcceptOutputWireAgreementLinear →
      Simulation.CompiledAcceptCircuitEvalAgreementLinear)

#check
  (Simulation.proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts :
    Simulation.PsubsetPpolyCompiledRuntimeLinearOutputContracts →
      ComplexityInterfaces.P_subset_PpolyDAG)

#check
  (Simulation.proved_P_subset_PpolyDAG_of_linearOutputAgreementAndLinearStepProvider :
    Simulation.CompiledAcceptOutputWireAgreementLinear →
      (∀ (M) (n : Nat),
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.StepCompiledLinearCandidateStepSpecProvider M n) →
      ComplexityInterfaces.P_subset_PpolyDAG)

end Pnp3.Tests
