import ConditionalSeparation.Conditional
import Pnp4.Tests.SingleResearchGapFinalSurfaceTests
namespace ConditionalSeparation.Audit
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion
-- Full-proposition mirrors elaborate independently and apply the original proofs.
theorem check_R_iff_original : ConditionalSeparation.OpenProblem.R ↔
    (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))) := ConditionalSeparation.R_iff_original

theorem check_close (hR : (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d)))) :
    ∃ k : Nat,
      UniformClassBridgeClosure.Ordinary.UniformNP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ UniformClassBridgeClosure.Ordinary.UniformP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) := ConditionalSeparation.close hR

#check (ConditionalSeparation.OpenProblem.R : Prop)
#check (ConditionalSeparation.R_iff_original : ConditionalSeparation.OpenProblem.R ↔ (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))))
#check (ConditionalSeparation.close : (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))) → ∃ k : Nat,
      UniformClassBridgeClosure.Ordinary.UniformNP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ UniformClassBridgeClosure.Ordinary.UniformP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))))
end ConditionalSeparation.Audit

#print axioms ConditionalSeparation.OpenProblem.R
#print axioms ConditionalSeparation.R_iff_original
#print axioms ConditionalSeparation.close
#print axioms ConditionalSeparation.Audit.check_R_iff_original
#print axioms ConditionalSeparation.Audit.check_close
#print axioms Pnp4.Frontier.ContractExpansion.single_research_gap_ordinary_separation
#print axioms Pnp4.Tests.SingleResearchGapFinal.check_single_research_gap_ordinary_separation
