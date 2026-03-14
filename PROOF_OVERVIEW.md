# Proof Overview (Auditor Guide)

Updated: 2026-03-13

This file is an auditor-oriented map of the active proof route in the current
repository state.

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current interim release posture:
`RELEASE_RC.md`.

## 1) Pipeline shape

Active code path is:

`SAL -> Covering/Lower Bounds -> anti-checker -> magnification -> DAG final wrappers`.

Final theorem interface is centralized in `pnp3/Magnification/FinalResult.lean`.

## 2) Final theorem ladder in code

Key active ladder:

1. `strictGapNPFamily_of_tmWitnesses`
2. `NP_not_subset_PpolyFormula_final*`
3. `NP_not_subset_PpolyReal_final*`
4. `P_ne_NP_final*`

## 3) Current explicit boundary assumptions

Default final endpoint `P_ne_NP_final` requires:

1. `NP_not_subset_PpolyDAG`

Constructive compatibility endpoint `P_ne_NP_final_of_default_supportBounds`
additionally carries:

1. `hasDefaultFormulaSupportRestrictionBoundsPartial`

## 4) Inclusion-side closure status (`P ⊆ PpolyDAG`)

Closed internals on linear compiled route:

1. `stepCompiledLinearCandidateStepSpecProvider_internal`
2. `compiledRuntimeCircuitSizeBoundLinear_internal`
3. `compiledRuntimeAcceptCorrectnessLinear_internal`
4. `compiledAcceptOutputWireAgreementLinear_internal`
5. no-arg endpoint `proved_P_subset_PpolyDAG_internal`

## 5) What is currently closed vs open

Closed:

1. Buildable active route and final wrappers.
2. Axiom/sorry hygiene for active `pnp3/`.
3. Step10 contract-surface tests for inclusion routes.

Open for unconditional in-repo `P ≠ NP`:

1. internalize `NP_not_subset_PpolyDAG` endpoint;
2. remove remaining external assumptions from default final wrappers.

## 6) Minimal audit script

```bash
./scripts/check.sh
for f in pnp3/Tests/Step10*.lean; do lake env lean "$f"; done
rg -n "^theorem P_ne_NP_final|^theorem NP_not_subset_PpolyReal_final|^theorem NP_not_subset_PpolyFormula_final" \
  pnp3/Magnification/FinalResult.lean
```

Then compare theorem signatures with `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## 7) Documentation policy

Use these files as source of truth:

1. `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`
2. `STATUS.md`
3. `TODO.md`
4. `AXIOMS_FINAL_LIST.md`

Historical notes in `archive/` are non-authoritative.
