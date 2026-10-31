import ConditionalSeparation.Equivalence
import Lean
namespace ConditionalSeparation.LightAudit
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion
/-- Exact full proposition; mechanical application, not an independent reproof. -/
theorem check_R_iff_original : ConditionalSeparation.OpenProblem.R ↔
    (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))) :=
  ConditionalSeparation.R_iff_original
#check (ConditionalSeparation.OpenProblem.R : Prop)
#check (ConditionalSeparation.R_iff_original : ConditionalSeparation.OpenProblem.R ↔
    (∃ k : Nat, ∀ d : Nat, ¬ Nonempty
      (Pnp4.Frontier.BoundedSearchSolver
        (treeProblem (treeCircuitWitnessCodec (thresholdPoly k)))
        C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))))
end ConditionalSeparation.LightAudit
#print axioms ConditionalSeparation.OpenProblem.R
#print axioms ConditionalSeparation.R_iff_original
#print axioms ConditionalSeparation.LightAudit.check_R_iff_original
open Lean Elab Command in
run_cmd do
  let roots : List Name := [``ConditionalSeparation.OpenProblem.R,
    ``ConditionalSeparation.R_iff_original,
    ``ConditionalSeparation.LightAudit.check_R_iff_original]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  for n in roots do
    unless env.contains n do throwError "absent direct root {n}"
    for a in (← collectAxioms n) do
      unless allowed.contains a do throwError "nonallowed transitive axiom {a}"
    logInfo m!"[CS_LIGHT_ROOT] {n}"
