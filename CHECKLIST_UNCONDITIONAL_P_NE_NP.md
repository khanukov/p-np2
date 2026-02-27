# Checklist: Unconditional Constructive `P ≠ NP`

Updated: 2026-02-27

This is the canonical checklist for what blocks an unconditional in-repo
constructive theorem `P ≠ NP`.

## Current final API (actual code)

File: `pnp3/Magnification/FinalResult.lean`

- `NP_not_subset_PpolyFormula_final_with_provider`
- `NP_not_subset_PpolyFormula_final`
- `NP_not_subset_PpolyFormula_final_of_formulaCertificate`
- `NP_not_subset_PpolyFormula_final_of_multiswitching_contract`
- `NP_not_subset_PpolyFormula_final_constructive`
- `NP_not_subset_PpolyFormula_final_of_supportBounds`
- `P_ne_NP_final_with_provider`
- `P_ne_NP_final`
- `P_ne_NP_final_of_formulaCertificate`
- `P_ne_NP_final_of_multiswitching_contract`
- `P_ne_NP_final_constructive`
- `P_ne_NP_final_of_supportBounds`
- helper: `strictGapNPFamily_of_tmWitnesses`

## Unconditional blockers (must be internalized)

Legacy wrapper `P_ne_NP_final` still requires:

1. `hasDefaultStructuredLocalityProviderPartial`
2. `AsymptoticFormulaTrackHypothesis`
3. `StrictGapNPFamily`
4. `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` (`hFormulaToPpoly`)

Active constructive endpoint `P_ne_NP_final_of_default_supportBounds` now
tracks this blocker set:

1. `hasDefaultFormulaSupportRestrictionBoundsPartial`
2. `AsymptoticFormulaTrackHypothesis`
3. `StrictGapNPFamily`
4. `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` (`hFormulaToPpoly`)

Explicit variant: `P_ne_NP_final_of_supportBounds`
(`FormulaSupportRestrictionBoundsPartial` as direct input).

Until the constructive blocker set is fully discharged internally, the
repository does **not** contain an unconditional theorem `P ≠ NP`.

## Proof-quality safety checks

Before deleting lemmas/routes, confirm:

1. `./scripts/check.sh` passes.
2. `pnp3/Tests/AxiomsAudit.lean` still reports 0 axioms.
3. Final endpoints listed above still compile and are reachable.
4. No document claims unconditional `P ≠ NP`.

## Definition of done (in-repo unconditional status)

All of the following must hold at once:

1. A theorem `P_ne_NP` is derivable without external bridge/provider hypotheses.
2. `P_ne_NP_final*` wrappers no longer require `hFormulaToPpoly`.
3. Remaining final route assumptions are either proved in-repo or eliminated.
4. `README.md`, `STATUS.md`, `TODO.md`, `AXIOMS_FINAL_LIST.md` are updated to
   state unconditional status explicitly and consistently.
