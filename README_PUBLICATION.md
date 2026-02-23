# PNP3: Publication-facing Status Snapshot

> **Updated:** 2026-02-23

This repository currently provides an AC0-focused machine-checked partial-track
pipeline in Lean 4.
Final `P != NP` wrappers are currently conditional on an explicit formula-to-`P/poly` bridge.

## Verified now

- Active `axiom` declarations in `pnp3/`: 0.
- Active `sorry/admit` in `pnp3/`: 0.
- Build and audit scripts pass.
- Localized bridge for `gapPartialMCSP_Language p` is internalized via
  `trivialFormulaizer`.
- Certificate-cardinality plumbing is automated in the main certificate route
  (`HalfTableCertificateBound`, `..._of_certificate_auto`).
- I-4 is constructively closed for explicit AC0/CNF inputs (Path A) via
  `pnp3/Magnification/AC0LocalityBridge.lean`.
- AC0-facing final theorem hooks are available:
  - `NP_not_subset_AC0_final`
  - `NP_not_subset_AC0_final_with_provider`
  - `NP_not_subset_AC0_final_of_engine`
  - fixed-parameter hooks:
    `NP_not_subset_AC0_at_param_with_provider`,
    `NP_not_subset_AC0_at_param_of_engine`
- Naming note:
  `...PpolyFormula_final...` theorems in `FinalResult.lean` should be read as
  AC0-route formula-separation wrappers, not as standalone global non-uniform
  separation claims.
- Bridge from explicit TM witness families to strict NP-family input:
  `strictGapNPFamily_of_tmWitnesses`.

## Complexity interface note (TM-faithful NP)

- Canonical `NP` in this repo is TM-based (`NP := NP_TM`, `NP_strict := NP_TM`).
- Partial-MCSP NP side is intentionally TM-only: no Lean-level verifier stubs are
  used as NP evidence.
- Constructive obligations are exposed through explicit witness packages
  (`GapPartialMCSP_TMWitness`, `GapPartialMCSP_Asymptotic_TMWitness`).

## Still external

1. General `PpolyFormula -> AC0` bridge (intentionally not claimed).
2. Default/global provider packaging remains explicit in some wrappers.
3. Formula-separation to non-uniform bridge (`hFormulaToPpoly`) for `P != NP`.

## Current scientific claim level

- Active strategic target: AC0-side separation route.
- `P != NP` wrappers are present but explicitly conditional on item (3).
- The assumption bundle is exposed in code as
  `ConditionalPneNpFinalContract` (`pnp3/Magnification/FinalResult.lean`).

## What External Researchers Need To Close

To turn the repository into an unconditional in-repo `P != NP` claim, the
remaining closure items are:

1. Internalize default constructive structured-provider availability from
   existing AC0 I-4 artifacts (I-2).
2. Internalize the bridge
   `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` and remove
   `hFormulaToPpoly` from final wrappers (I-5).

Optional (separate layer, not required for I-4):
3. Add explicit stronger bridge assumptions/modules (Option-C style) for
   broader non-AC0 fronts.

Minimal in-repo completion check:
- `./scripts/check.sh` passes.
- Final `P != NP` theorem family no longer requires external bridge arguments.

For full technical status, use `STATUS.md` and `AXIOMS_FINAL_LIST.md`.
