# Proof Overview (Auditor Guide)

Updated: 2026-02-27

This file is an auditor-oriented map of the active proof route in the current
repository state.

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## 1) Pipeline shape

Active code path is:

`SAL -> Covering-Power -> anti-checker -> magnification`.

The final theorem interface is centralized in
`pnp3/Magnification/FinalResult.lean`.

## 2) Final theorem ladder in code

Main route in `FinalResult.lean`:

1. `StrictGapNPFamily`
2. `strictGapNPFamily_of_tmWitnesses`
3. `AsymptoticFormulaTrackHypothesis`
4. `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis`
5. `NP_not_subset_PpolyFormula_final_with_provider`
6. `NP_not_subset_PpolyFormula_final`
7. `P_ne_NP_final_with_provider`
8. `P_ne_NP_final`

Certificate-first variants:

- `NP_not_subset_PpolyFormula_final_of_formulaCertificate`
- `P_ne_NP_final_of_formulaCertificate`

## 3) Where each assumption comes from

`P_ne_NP_final` assumptions and source modules:

1. `hasDefaultStructuredLocalityProviderPartial`
   - source: `pnp3/Magnification/LocalityProvider_Partial.lean`
2. `AsymptoticFormulaTrackHypothesis`
   - source: `pnp3/Magnification/FinalResult.lean`
3. `StrictGapNPFamily`
   - source: `pnp3/Magnification/FinalResult.lean`
   - constructive helper from TM witnesses:
     `strictGapNPFamily_of_tmWitnesses`
4. `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`
   - external bridge assumption on the final step.

## 4) Core constructive components

TM/NP side:

- `pnp3/Models/Model_PartialMCSP.lean`

Lower-bound/anti-checker side:

- `pnp3/LowerBounds/AntiChecker_Partial.lean`
- `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean`
- `pnp3/Magnification/PipelineStatements_Partial.lean`

Bridge/provider side:

- `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`
- `pnp3/Magnification/LocalityProvider_Partial.lean`
- `pnp3/Magnification/AC0LocalityBridge.lean`

## 5) What is currently closed vs open

Closed in current codebase:

1. Buildable active route with explicit final wrappers.
2. Axiom/sorry hygiene for `pnp3/`.
3. Contract-style decomposition of remaining obligations.

Open for unconditional in-repo `P ≠ NP`:

1. Internalize provider/asymptotic/NP-family assumptions.
2. Internalize formula-track to non-uniform bridge:
   `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.

## 6) Minimal audit script

```bash
./scripts/check.sh
rg -n "theorem P_ne_NP_final|theorem NP_not_subset_PpolyFormula_final" \
  pnp3/Magnification/FinalResult.lean
```

Then compare theorem signatures with
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## 7) Documentation policy

Use these files as source of truth:

1. `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`
2. `STATUS.md`
3. `TODO.md`
4. `AXIOMS_FINAL_LIST.md`

Historical or local notes are non-authoritative.
