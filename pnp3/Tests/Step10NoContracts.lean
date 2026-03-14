import Complexity.Simulation.Circuit_Compiler

namespace Pnp3.Tests

open Pnp3.Complexity

#check
  (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidateStepSpecProvider_internal :
    ∀ (M) (n : Nat),
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.StepCompiledLinearCandidateStepSpecProvider M n)

#check
  (Simulation.compiledRuntimeAcceptCorrectnessLinear_internal :
    Simulation.CompiledRuntimeAcceptCorrectnessLinear)

#check
  (Simulation.compiledAcceptOutputWireAgreementLinear_internal :
    Simulation.CompiledAcceptOutputWireAgreementLinear)

#check
  (Simulation.proved_P_subset_PpolyDAG_of_linearOutputAgreementAndLinearStepProvider :
    Simulation.CompiledAcceptOutputWireAgreementLinear →
      (∀ (M) (n : Nat),
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.StepCompiledLinearCandidateStepSpecProvider M n) →
      ComplexityInterfaces.P_subset_PpolyDAG)

#check
  (Simulation.proved_P_subset_PpolyDAG_internal :
    ComplexityInterfaces.P_subset_PpolyDAG)

end Pnp3.Tests
