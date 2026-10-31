import ConditionalSeparation.Audit
import ConditionalSeparation.LightAudit
import Lean

/-! Direct roots for the package's public API and accepted original endpoint.
Mirrors check independently elaborated full propositions, not independent reproofs.
-/
open Lean Elab Command in
run_cmd do
  let requested : List Name := [
    ``ConditionalSeparation.OpenProblem.R,
    ``ConditionalSeparation.R_iff_original,
    ``ConditionalSeparation.close,
    ``ConditionalSeparation.Audit.check_R_iff_original,
    ``ConditionalSeparation.Audit.check_close,
    ``ConditionalSeparation.LightAudit.check_R_iff_original,
    ``Pnp4.Frontier.ContractExpansion.single_research_gap_ordinary_separation,
    ``Pnp4.Tests.SingleResearchGapFinal.check_single_research_gap_ordinary_separation]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  for n in requested do
    unless env.contains n do throwError "absent direct root {n}"
    let axs ← collectAxioms n
    for a in axs do
      unless allowed.contains a do throwError "nonallowed transitive axiom {a} for {n}"
    logInfo m!"[CS_PACKAGE_ROOT] {n}"
    for a in axs do logInfo m!"[CS_PACKAGE_AXIOM] {n} {a}"
