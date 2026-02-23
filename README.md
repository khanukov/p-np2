# P!=NP formalization repository

> **Status (2026-02-23):** `pnp3/` builds, has **0 active `axiom`** and **0 `sorry/admit`**, with AC0-focused machine-checked separation hooks.

This repository contains the Lean 4 formalization around the PNP3 pipeline:

`SAL -> Covering-Power -> anti-checker -> magnification`

## Current proved surface

- Strategic target class: `AC^0`.
- AC0-oriented final hooks are present in `pnp3/Magnification/FinalResult.lean`:
  - `NP_not_subset_AC0_final`
  - `NP_not_subset_AC0_final_with_provider`
  - `NP_not_subset_AC0_final_of_engine`
  - TM-witness variants:
    `NP_not_subset_AC0_final_with_provider_of_tmWitnesses`,
    `NP_not_subset_AC0_final_of_engine_of_tmWitnesses`
  - fixed-parameter strict hooks:
    `NP_not_subset_AC0_at_param_with_provider`,
    `NP_not_subset_AC0_at_param_of_engine`
  - fixed-parameter TM-witness variants:
    `NP_not_subset_AC0_at_param_with_provider_of_tmWitness`,
    `NP_not_subset_AC0_at_param_of_engine_of_tmWitness`
- Localized bridge `PpolyReal -> PpolyFormula` for `gapPartialMCSP_Language p` is internalized via:
  - `trivialFormulaizer`
  - `gapPartialMCSP_realization_trivial`

## Complexity-interface status (TM-faithful NP)

- Canonical NP interface is now TM-based: `NP := NP_TM` and `NP_strict := NP_TM`
  in `pnp3/Complexity/Interfaces.lean`.
- For Partial-MCSP we intentionally keep only TM-strict NP obligations and
  explicit witness packages:
  - `GapPartialMCSP_TMWitness`
  - `GapPartialMCSP_Asymptotic_TMWitness`
- Lean-level verifier stubs (`gapPartialMCSP_verify*`) and policy-only aliases
  were removed from `pnp3/Models/Model_PartialMCSP.lean` to avoid any
  non-TM/vacuous reading of NP-membership.

## I-4 status (release note)

- I-4 is constructively closed for the explicit AC0/CNF route (Path A).
- Entry module: `pnp3/Magnification/AC0LocalityBridge.lean`.
- The project intentionally does **not** claim a general conversion
  `PpolyFormula -> AC0`.

## Remaining external inputs (non-axiomatic)

1. Default/global provider packaging remains explicit in some wrappers
   (`hasDefaultStructuredLocalityProviderPartial` style inputs).
2. Formula-to-`P/poly` bridge for final `P != NP` wrapper
   (`hFormulaToPpoly` in `FinalResult.lean`).

## Important scope note

- AC0-core separation route is the active target and is fully axiom-clean.
- No claim is made about a global `PpolyFormula -> AC0` conversion.
- `P != NP` wrappers remain conditional on the explicit bridge
  `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.

## Recommended Theorem Ladder

Most constructive practical route:

1. Provide explicit `GapPartialMCSP_TMWitness` data (fixed-`p` or family).
2. Use explicit `ConstructiveLocalityEnginePartial` (avoid default `Nonempty` wrappers).
3. Use fixed-parameter theorem
   `NP_not_subset_AC0_at_param_of_engine_of_tmWitness`
   when you work at one concrete `p`.
4. Use asymptotic theorem
   `NP_not_subset_AC0_final_of_engine_of_tmWitnesses`
   when you have full witness family data.

## What Is Still Needed For An Unconditional Final Claim

This section is intended for external researchers who want to push this project
to a mathematically final state.

### Code-level closure criteria (inside this repository)

1. Close I-2 (default constructive provider path).
- Derive `hasDefaultStructuredLocalityProviderPartial` from internal certificate
  providers for formula-extracted solvers.
- Target module: `pnp3/Magnification/LocalityProvider_Partial.lean`.

2. Close I-5 (formula-track to `P/poly` bridge).
- Internalize a sound theorem of shape:
  `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.
- Remove the external bridge argument `hFormulaToPpoly` from
  `P_ne_NP_final*` wrappers in `pnp3/Magnification/FinalResult.lean`.

### Minimal acceptance check for an internal unconditional status

1. `./scripts/check.sh` passes with no new external gates.
2. Active final theorem for `P != NP` no longer requires `hFormulaToPpoly`.
3. `STATUS.md`, `AXIOMS_FINAL_LIST.md`, and `TODO.md` reflect that closure
   without conditional wording for the final claim.

### External scientific recognition (outside code)

Even after full in-repo closure, official recognition still requires the
standard research process: public write-up, independent expert review,
replication, and broad community acceptance.

## Docs to use

- `STATUS.md` (single source of truth)
- `TODO.md` (current execution order)
- `AXIOMS_FINAL_LIST.md` (external input inventory)
- `FAQ.md`
- `BARRIER_AUDIT.md` (explicit barrier-status matrix)

## Build

```bash
lake exe cache get
lake build
lake test
./scripts/check.sh
```
