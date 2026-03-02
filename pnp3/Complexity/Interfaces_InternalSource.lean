import Complexity.Interfaces
import Complexity.Simulation.Circuit_Compiler

namespace Pnp3
namespace ComplexityInterfaces

/--
Interface-level alias for the bridged iterated internal contract bundle.

This lives outside `Complexity/Interfaces.lean` to avoid import cycles.
-/
abbrev PsubsetPpolyInternalContractsBridged : Prop :=
  Pnp3.Complexity.Simulation.PsubsetPpolyInternalContractsIteratedBridged

/--
Interface-level alias for the runtime-only iterated bridged bundle.
-/
abbrev PsubsetPpolyInternalContractsIteratedRuntimeOnly : Prop :=
  Pnp3.Complexity.Simulation.PsubsetPpolyInternalContractsIteratedRuntimeOnly

/--
Canonical iterated contract alias for the active internal-source DAG route.
-/
abbrev PsubsetPpolyInternalContractsIterated : Prop :=
  Pnp3.Complexity.Simulation.PsubsetPpolyInternalContractsIteratedCanonical

/--
Interface-level alias for compiled-runtime residual contracts.
-/
abbrev PsubsetPpolyCompiledRuntimeContracts : Prop :=
  Pnp3.Complexity.Simulation.PsubsetPpolyCompiledRuntimeContracts

/--
Default internal-source contract bundle for DAG inclusion.

This variant intentionally avoids the legacy runtime-config bridge
`RuntimeConfigEqStepCompiled` and the global evaluator-agreement contract.
-/
abbrev PsubsetPpolyInternalContractsInternal : Prop :=
  Pnp3.Complexity.Simulation.InternalCompiler.RuntimeSpecProvider

/--
Internal-source DAG inclusion route exposed at the interface layer.
-/
theorem P_subset_PpolyDAG_internal_source
    (hContracts : PsubsetPpolyInternalContractsInternal) :
    P_subset_PpolyDAG :=
  Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_of_runtimeOnly
    hContracts

/--
Interface wrapper for the final DAG-track nonuniform separation step via the
internal-source contract bundle.
-/
theorem P_ne_NP_of_nonuniform_dag_separation_internal_source
    (hNP : NP_not_subset_PpolyDAG)
    (hContracts : PsubsetPpolyInternalContractsInternal) :
    P_ne_NP :=
  P_ne_NP_of_nonuniform_dag_separation hNP
    (P_subset_PpolyDAG_internal_source hContracts)

/--
Compatibility endpoint keeping the iterated-bridged contract route available.
-/
theorem P_subset_PpolyDAG_internal_source_bridged
    (hContracts : PsubsetPpolyInternalContractsBridged) :
    P_subset_PpolyDAG :=
  Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_of_iteratedContractsBridged
    hContracts

/--
Iterated runtime endpoint without global evaluator-agreement contract.
-/
theorem P_subset_PpolyDAG_internal_source_iterated_runtimeOnly
    (hContracts : PsubsetPpolyInternalContractsIteratedRuntimeOnly) :
    P_subset_PpolyDAG :=
  Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_of_iteratedRuntimeOnlyContracts
    hContracts

/--
Canonical iterated internal-source endpoint.
-/
theorem P_subset_PpolyDAG_internal_source_iterated
    (hContracts : PsubsetPpolyInternalContractsIterated) :
    P_subset_PpolyDAG :=
  Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_of_iteratedCanonicalContracts
    hContracts

/--
Compatibility endpoint for the compiled-runtime residual contract route.
-/
theorem P_subset_PpolyDAG_internal_source_compiledRuntime
    (hContracts : PsubsetPpolyCompiledRuntimeContracts) :
    P_subset_PpolyDAG :=
  Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_of_compiledRuntimeContracts
    hContracts

end ComplexityInterfaces
end Pnp3
