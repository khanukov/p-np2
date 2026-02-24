# P!=NP formalization repository

> **Status (2026-02-23):** `pnp3/` builds, has **0 active `axiom`** and **0 `sorry/admit`**, with AC0-focused machine-checked separation hooks.
> Final `P != NP` wrappers in `FinalResult.lean` are currently conditional on an explicit non-AC0 bridge.

This repository contains the Lean 4 formalization around the PNP3 pipeline:

`SAL -> Covering-Power -> anti-checker -> magnification`

## Current proved surface

- Strategic target class: `AC^0`.
- Active constructive-semantic hooks are present in `pnp3/Magnification/FinalResult.lean`:
  - fixed-parameter semantic entrypoints:
    `NP_not_subset_PpolyFormula_from_params_semantic`,
    `NP_not_subset_PpolyFormula_from_params_semantic_of_syntacticEasy`
  - asymptotic semantic entrypoints:
    `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic`,
    `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic_of_syntacticEasy`
  - final wrappers:
    `NP_not_subset_PpolyFormula_final`,
    `P_ne_NP_final`
- Naming note:
  theorem names with `...PpolyFormula_final...` in `FinalResult.lean` are
  AC0-route formula-separation wrappers, not standalone global non-uniform
  separation claims.
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
- A single bundled interface for those assumptions is available as
  `ConditionalPneNpFinalContract` in `pnp3/Magnification/FinalResult.lean`.

## Recommended Theorem Ladder

Most constructive practical route:

1. Provide explicit `GapPartialMCSP_TMWitness` data (fixed-`p` or family).
2. Use explicit `ConstructiveLocalityEnginePartial` (avoid default `Nonempty` wrappers).
3. Build semantic Step-C at fixed parameter via
   `NP_not_subset_PpolyFormula_from_params_semantic_of_syntacticEasy`.
4. Lift to asymptotic via
   `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic_of_syntacticEasy`
   and then to `P_ne_NP_final` (still with explicit non-AC0 bridge).

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

## Build

```bash
lake exe cache get
lake build
lake test
./scripts/check.sh
```
