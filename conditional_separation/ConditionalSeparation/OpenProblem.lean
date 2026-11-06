import Pnp4.Frontier.ContractExpansion.ThresholdGrowth
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.C_DAG_Adapter
import Pnp4.Frontier.SearchMCSPConcreteTargets

/-! Exact research premise. The search problem below expands the accepted
`treeProblem` abbreviation without importing its greedy implementation.
No proof of this substantial nonuniform promise-search lower bound is supplied. -/
namespace ConditionalSeparation.OpenProblem
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion

/-- One fixed threshold precedes every degree; sizes are per output bit,
polynomial in the full truth-table length, with correctness only on promise. -/
def R : Prop :=
  ∃ k : Nat, ∀ d : Nat, ¬ Nonempty
    (BoundedSearchSolver
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))

#check (R : Prop)
end ConditionalSeparation.OpenProblem
#print axioms ConditionalSeparation.OpenProblem.R
