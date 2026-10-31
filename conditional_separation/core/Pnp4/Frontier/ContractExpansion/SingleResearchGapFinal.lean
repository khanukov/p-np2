import Pnp4.Frontier.ContractExpansion.SingleResearchGap
import UniformClassBridgeClosure.OrdinaryPpolyDAG

/-! Direct Ordinary-model conditional separation for one fixed threshold/codec/language.
The sole research premise below is unproved. SG1 discharges concrete growth and
Ordinary-NP membership; SG5 supplies unconditional Ordinary-P to canonical DAGs.
This composition fills no legacy ContentVerifierBridge and claims no unconditional
separation, nonvacuity, independent lower-bound proof, or release acceptance. -/
namespace Pnp4.Frontier.ContractExpansion

/-- One fixed k precedes all degrees, and the same language satisfies all three claims. -/
theorem single_research_gap_ordinary_separation
    (hResearch : ∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        Pnp4.Frontier.ContractExpansion.C_DAG
        (fun n => (Pnp3.Models.Partial.tableLen n) ^ d + d))) :
    ∃ k : Nat,
      UniformClassBridgeClosure.Ordinary.UniformNP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ UniformClassBridgeClosure.Ordinary.UniformP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := by
  obtain ⟨k, hNP, hNotCircuit⟩ := exists_ordinaryNP_and_not_PpolyDAG_treePoly hResearch
  refine ⟨k, hNP, hNotCircuit, ?_⟩
  intro hP
  exact hNotCircuit (UniformClassBridgeClosure.Ordinary.uniformP_ppolyDAG _ hP)

end Pnp4.Frontier.ContractExpansion
