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
Internal-source DAG inclusion route exposed at the interface layer.
-/
theorem P_subset_PpolyDAG_internal_source
    (hContracts : PsubsetPpolyInternalContractsBridged) :
    P_subset_PpolyDAG :=
  Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_of_iteratedContractsBridged
    hContracts

/--
Interface wrapper for the final DAG-track nonuniform separation step via the
internal-source contract bundle.
-/
theorem P_ne_NP_of_nonuniform_dag_separation_internal_source
    (hNP : NP_not_subset_PpolyDAG)
    (hContracts : PsubsetPpolyInternalContractsBridged) :
    P_ne_NP :=
  P_ne_NP_of_nonuniform_dag_separation hNP
    (P_subset_PpolyDAG_internal_source hContracts)

end ComplexityInterfaces
end Pnp3

