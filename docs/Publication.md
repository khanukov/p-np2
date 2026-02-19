# Publication Contract

Last updated: 2026-02-19

This file defines what can be claimed from the active, machine-checked development as it exists now.

## What is fully machine-checked
- The A->B->C->D logical pipeline in `pnp3/` type-checks end-to-end.
- The derivation schema
  - `NP ⊄ P/poly`
  - `P ⊆ P/poly`
  - therefore `P ≠ NP`
  is formalized and checked.
- Core and anti-checker cones are audited for project-specific axiom absence.

Canonical theorem chain used in publication-facing statements:
- `P_ne_NP_final_asymptotic`
- `P_ne_NP_from_partial_formulas_realized`
- `NP_not_subset_Ppoly_from_partial_formulas_realized`
- `OPS_trigger_formulas_partial_realized`
- `OPS_trigger_general_contra_partial_realized`
- `LB_GeneralFromLocal_partial_realized`
- `LB_LocalCircuits_core_partial_realized`

## What is conditional
There are currently no project-specific axioms in `pnp3/`.

The final theorem cone (`P_ne_NP_final_asymptotic`) is still conditional through explicit
hypotheses in theorem statements (for example
`LocalizedFamilyWitnessHypothesis_partial_realized` inside
`MagnificationAssumptions`), so the claim remains conditional rather than
an unconditional internal proof.

## External imports
- `P ⊆ P/poly` is imported through `ThirdPartyFacts.PsubsetPpoly` from `Facts/PsubsetPpoly`.
- This is tracked by axiom/dependency audits and should be stated explicitly in publication-facing text.

## Witness-interface caveat
`FamilyIsAC0` and `FamilyIsLocalCircuit` are witness predicates (`Nonempty` wrappers).
They are not axioms, but they encode substantive obligations unless witness constructors are internalized.

## Hard constraints for public claims
Do not claim any of the following unless P0 in `docs/Roadmap.md` is complete:
- unconditional in-repo proof of `P ≠ NP`
- removal of all project-specific external scaffolding in final cone

## Required reproducibility checks
Before publishing any status update, run:
1. `lake build`
2. `bash scripts/check.sh`
3. `bash scripts/audit_handoff.sh` (for attachable audit logs)

The release note must include:
- exact axiom inventory reported by `check.sh`
- whether project-specific axioms are present in `pnp3/`
- hash/date of the run

## Documentation quality gate
Any publication-status update must keep the following in sync:
- `docs/CurrentState.md` (technical status and dependency cone)
- `docs/Roadmap.md` (next technical blockers)
- `docs/Publication.md` (claim boundary text)
