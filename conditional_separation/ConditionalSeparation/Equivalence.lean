import ConditionalSeparation.OpenProblem

namespace ConditionalSeparation
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion

/-- Definitional expansion, not a weaker or stronger search problem. -/
theorem R_iff_original : OpenProblem.R ↔
    (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (BoundedSearchSolver (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))) := Iff.rfl

end ConditionalSeparation
