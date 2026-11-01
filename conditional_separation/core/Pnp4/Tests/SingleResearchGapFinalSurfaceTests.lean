import Pnp4.Frontier.ContractExpansion.SingleResearchGapFinal

/-! Complete independently elaborated final proposition and explicit type pins.
The mirror applies the original theorem; it is not an independent reproof. -/
namespace Pnp4.Tests.SingleResearchGapFinal
open Pnp4.Frontier.ContractExpansion

theorem check_single_research_gap_ordinary_separation
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
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) :=
  single_research_gap_ordinary_separation hResearch

#check (single_research_gap_ordinary_separation :
    (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        Pnp4.Frontier.ContractExpansion.C_DAG
        (fun n => (Pnp3.Models.Partial.tableLen n) ^ d + d))) →
    ∃ k : Nat,
      UniformClassBridgeClosure.Ordinary.UniformNP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ UniformClassBridgeClosure.Ordinary.UniformP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))))

#check (check_single_research_gap_ordinary_separation :
    (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        Pnp4.Frontier.ContractExpansion.C_DAG
        (fun n => (Pnp3.Models.Partial.tableLen n) ^ d + d))) →
    ∃ k : Nat,
      UniformClassBridgeClosure.Ordinary.UniformNP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ UniformClassBridgeClosure.Ordinary.UniformP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))))

end Pnp4.Tests.SingleResearchGapFinal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : List Name := [
    ``Pnp4.Frontier.ContractExpansion.single_research_gap_ordinary_separation,
    ``Pnp4.Tests.SingleResearchGapFinal.check_single_research_gap_ordinary_separation,
    ``Pnp4.Frontier.ContractExpansion.exists_ordinaryNP_and_not_PpolyDAG_treePoly,
    ``UniformClassBridgeClosure.Ordinary.uniformP_ppolyDAG]
  for n in roots do
    unless env.contains n do throwError "missing SG6 direct root {n}"
    logInfo m!"[SG6_REQUEST] {n}"
  for n in env.header.moduleNames do
    logInfo m!"[SG6_HEADER] {n}"

#print axioms Pnp4.Frontier.ContractExpansion.single_research_gap_ordinary_separation
#print axioms Pnp4.Tests.SingleResearchGapFinal.check_single_research_gap_ordinary_separation
#print axioms Pnp4.Frontier.ContractExpansion.exists_ordinaryNP_and_not_PpolyDAG_treePoly
#print axioms UniformClassBridgeClosure.Ordinary.uniformP_ppolyDAG
