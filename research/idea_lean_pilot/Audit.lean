import Attempt.Fixtures
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let requested : List Name := [
    `Research.IdeaLeanPilot.BudgetWitness,
    `Research.IdeaLeanPilot.AllBoundedAccept,
    `Research.IdeaLeanPilot.budget_witness,
    `Research.IdeaLeanPilot.not_all_bounded_accept,
    `Research.IdeaLeanPilot.check_budget_witness,
    `Research.IdeaLeanPilot.check_not_all_bounded_accept]
  let mut observed : List Name := []
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let some owner := env.header.moduleNames[idx.toNat]? | throwError "owner bounds"
      if (`Attempt).isPrefixOf owner then
        unless requested.contains n do throwError "unexpected pilot declaration {n}"
        observed := n :: observed
  for n in requested do
    unless observed.contains n do throwError "missing pilot declaration {n}"
    for a in (← collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "nonallowed pilot axiom {a} for {n}"
    logInfo m!"[IDEA_PILOT_ROOT] {n}"
    elabCommand (← `(#print axioms $(mkIdent n)))
