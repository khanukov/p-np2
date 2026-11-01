import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP
import Complexity.Interfaces
import Complexity.Simulation.Circuit_Compiler

namespace Pnp4
namespace AlgorithmsToLowerBounds

/-- Final-bridge language type imported from the existing `pnp3` interfaces. -/
abbrev DagLanguage := Pnp3.ComplexityInterfaces.Language

/--
Explicit source package for the honest final bridge:
an `NP` language together with a verified `PpolyDAG` lower bound.
-/
structure VerifiedNPDAGLowerBoundSource where
  L : DagLanguage
  inNP : Pnp3.ComplexityInterfaces.NP L
  notInPpolyDAG : ¬ Pnp3.ComplexityInterfaces.PpolyDAG L

/--
Any explicit source witness yields the canonical DAG-separation target
`NP ⊄ PpolyDAG`.
-/
theorem NP_not_subset_PpolyDAG_of_verified_source
    (src : VerifiedNPDAGLowerBoundSource) :
    Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG :=
  ⟨src.L, src.inNP, src.notInPpolyDAG⟩

/--
Honest downstream bridge to `P ≠ NP`, using only:

1. the explicit `NP ⊄ PpolyDAG` witness derived from `src`;
2. the already-verified internal theorem `P ⊆ PpolyDAG`.
-/
theorem P_ne_NP_of_verified_source
    (src : VerifiedNPDAGLowerBoundSource) :
    Pnp3.ComplexityInterfaces.P_ne_NP := by
  exact Pnp3.ComplexityInterfaces.P_ne_NP_of_nonuniform_dag_separation
    (NP_not_subset_PpolyDAG_of_verified_source src)
    Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_internal

end AlgorithmsToLowerBounds
end Pnp4
