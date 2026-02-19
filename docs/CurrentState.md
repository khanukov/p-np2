# Current State

Last updated: 2026-02-19

## Scope
Active formalization is the `pnp3/` tree (Partial-MCSP pipeline).
Legacy work is in `archive/` and `old_attempts/` and is not part of the active proof cone.

## Pipeline status (A -> B -> C -> D)
- Part A (Shrinkage/SAL): implemented and machine-checked.
- Part B (Counting/Covering-Power): implemented and machine-checked.
- Part C (Anti-checker): implemented in constructive large-`Y` certificate form; no `False.elim` in critical partial cone files.
- Part D (Magnification bridge): implemented and machine-checked.

Key theorem anchors:
- Part A/B scenario glue:
  - `pnp3/LowerBounds/LB_Formulas.lean` (`scenarioFromAC0`, `scenarioFromLocalCircuit`, capacity lemmas)
- Part C:
  - `pnp3/LowerBounds/AntiChecker_Partial.lean`
    (`antiChecker_largeY_certificate_partial`, `antiChecker_largeY_certificate_local_partial`,
    `noSmallAC0Solver_partial`, `noSmallLocalCircuitSolver_partial`)
  - `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean`
  - `pnp3/LowerBounds/LB_LocalCircuits_Partial.lean`
- Part D:
  - `pnp3/LowerBounds/LB_GeneralFromLocal_Partial.lean`
  - `pnp3/Magnification/Facts_Magnification_Partial.lean`
  - `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`

Final theorem entry points:
- `pnp3/Magnification/FinalResult.lean` (`P_ne_NP_final_asymptotic`, `P_ne_NP_final`)

## Conditional vs unconditional status
The final theorem is currently **conditional** on one project-specific axiom:
- `localizedFamilyWitness_partial`
  - file: `pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`

This is automatically enforced by `scripts/check.sh` and `pnp3/Tests/AxiomsAudit.lean`.

## Active axiom inventory
Current expected project axioms in `pnp3/`: exactly 1
- `ThirdPartyFacts.localizedFamilyWitness_partial`

Automated check:
- `scripts/check.sh` validates axiom count and exact final-cone dependencies.

## Witness interfaces (not axioms)
The following are interface predicates requiring witness construction/hypotheses:
- `FamilyIsAC0`
- `FamilyIsLocalCircuit`

Defined in:
- `pnp3/ThirdPartyFacts/Facts_Switching.lean`

These are not axioms, but they remain substantive external obligations until fully internalized.

## Proof-cone map (current)
- `FinalResult` -> `Bridge_to_Magnification_Partial`
- `Bridge_to_Magnification_Partial` -> `Facts_Magnification_Partial`
- `Facts_Magnification_Partial` -> `LB_GeneralFromLocal_partial`
- `LB_GeneralFromLocal_partial` -> `LB_LocalCircuits_core_partial`
- `LB_LocalCircuits_core_partial` and `LB_Formulas_core_partial` -> `AntiChecker_Partial` + `LB_Formulas`

Operationally for final theorem:
- `P_ne_NP_final_asymptotic`
  -> `P_ne_NP_from_partial_formulas`
  -> `NP_not_subset_Ppoly_from_partial_formulas`
  -> `OPS_trigger_formulas_partial`
  -> `OPS_trigger_general_contra_partial`
  -> `LB_GeneralFromLocal_partial`
  -> `LB_LocalCircuits_core_partial`.

## What was recently cleaned up
- Removed duplicate audit docs and dead wrappers from active cone.
- Consolidated anti-checker into constructive large-`Y` certificate flow.
- Added dedicated anti-checker cone audit and CI guard for `False.elim` absence in critical files.

## How to verify locally
1. `lake build`
2. `bash scripts/check.sh`

`check.sh` validates:
- no `sorry`/`admit` in `pnp3/`
- exact project axiom count
- exact final/core/anti-checker axiom dependency signatures
- no `False.elim` in critical anti-checker partial files
- publication-gap doc consistency
