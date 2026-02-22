# P!=NP formalization repository

> **Status (2026-02-22):** `pnp3/` builds, has **0 active `axiom`** and **0 `sorry/admit`**, and provides a machine-checked **conditional** formula-track pipeline.

This repository contains the Lean 4 formalization around the PNP3 pipeline:

`SAL -> Covering-Power -> anti-checker -> magnification`

## Current proved surface

- Active final formula-track endpoint: `NP_not_subset_PpolyFormula` (conditional).
- Asymptotic entrypoints are present in `pnp3/Magnification/FinalResult.lean`.
- Localized bridge `PpolyReal -> PpolyFormula` for `gapPartialMCSP_Language p` is internalized via:
  - `trivialFormulaizer`
  - `gapPartialMCSP_realization_trivial`

## I-4 status (release note)

- I-4 is constructively closed for the explicit AC0/CNF route (Path A).
- Entry module: `pnp3/Magnification/AC0LocalityBridge.lean`.
- The project intentionally does **not** claim a general conversion
  `PpolyFormula -> AC0`.

## Remaining external inputs (non-axiomatic)

1. Provider-level certificate packages for formula-extracted general solvers
   (`FormulaCertificateProviderPartial`) or equivalent default availability.
2. Formula-to-`P/poly` bridge for final `P != NP` wrapper
   (`hFormulaToPpoly` in `FinalResult.lean`).

## Important scope note

- `NP_not_subset_PpolyFormula` is the current active separation target.
- `P != NP` wrappers exist, but remain conditional on the explicit bridge
  `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`.

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
