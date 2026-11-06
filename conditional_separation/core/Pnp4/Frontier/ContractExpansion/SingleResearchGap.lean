import FullFinalClosure.Surface
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionTransfer
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

/-!
SG1: same-language conditional composition for the approved direct Ordinary-TM0 route.
The fixed threshold/codec is chosen before every excluded circuit degree. The
circuit lower bound remains a premise, not a proved result. This infrastructure
composition does not fill the historical ContentVerifierBridge, prove Ordinary-P
simulation by DAG circuits, or prove P != NP. Route-policy reconciliation and all
integrated review/release gates remain separate obligations.
-/
namespace Pnp4.Frontier.ContractExpansion

/-- Concrete growth is discharged internally; only the stated circuit premise remains. -/
theorem ordinaryNP_and_not_PpolyDAG_treePoly (k : Nat)
    (hNoPoly : ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        Pnp4.Frontier.ContractExpansion.C_DAG
        (fun n => (Pnp3.Models.Partial.tableLen n) ^ d + d))) :
    UniformClassBridgeClosure.Ordinary.UniformNP
      (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG
      (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := by
  exact ⟨FullFinalClosure.ordinary_uniformNP_full k,
    not_PpolyDAG_contentPrefixExtension_of_noPolynomialBoundedSearchSolver
      (treeCircuitWitnessCodec (thresholdPoly k))
      (treePolynomialWitnessCodec (thresholdPoly k)
        (polyBoundedInTable_thresholdPoly k)).toGrowthAssumptions hNoPoly⟩

/-- A single fixed codec/language is chosen before all polynomial degrees. -/
theorem exists_ordinaryNP_and_not_PpolyDAG_treePoly (hResearch : ∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        Pnp4.Frontier.ContractExpansion.C_DAG
        (fun n => (Pnp3.Models.Partial.tableLen n) ^ d + d))) :
    ∃ k : Nat,
      UniformClassBridgeClosure.Ordinary.UniformNP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := by
  obtain ⟨k, hNoPoly⟩ := hResearch
  exact ⟨k, ordinaryNP_and_not_PpolyDAG_treePoly k hNoPoly⟩

end Pnp4.Frontier.ContractExpansion
