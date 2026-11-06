import ConditionalSeparation.Equivalence
import Pnp4.Frontier.ContractExpansion.SingleResearchGapFinal

namespace ConditionalSeparation
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion

/-- Conditional only: the sole substantial research premise remains unproved. -/
theorem close (hR : OpenProblem.R) :
    ∃ k : Nat,
      UniformClassBridgeClosure.Ordinary.UniformNP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) ∧
      ¬ UniformClassBridgeClosure.Ordinary.UniformP
        (ContentPrefixExtensionLanguage (treeCircuitWitnessCodec (thresholdPoly k))) :=
  single_research_gap_ordinary_separation (R_iff_original.mp hR)

end ConditionalSeparation
