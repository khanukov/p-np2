# PNP3: Publication-facing Status Snapshot

> **Updated:** 2026-02-22

This repository currently provides a machine-checked, conditional partial-track
pipeline in Lean 4.

## Verified now

- Active `axiom` declarations in `pnp3/`: 0.
- Active `sorry/admit` in `pnp3/`: 0.
- Build and audit scripts pass.
- Localized bridge for `gapPartialMCSP_Language p` is internalized via
  `trivialFormulaizer`.
- Certificate-cardinality plumbing is automated in the main certificate route
  (`HalfTableCertificateBound`, `..._of_certificate_auto`).

## Still external

1. Multi-switching/shrinkage witness construction for target solver families.
2. Provider-level certificate packages (`FormulaCertificateProviderPartial`) or
   equivalent default instances.
3. Formula-separation to non-uniform bridge (`hFormulaToPpoly`) for `P != NP`.

## Current scientific claim level

- Active final target: conditional `NP_not_subset_PpolyFormula`.
- `P != NP` wrappers are present but explicitly conditional on item (3).

## What External Researchers Need To Close

To turn the repository into an unconditional in-repo `P != NP` claim, the
remaining closure items are:

1. Internalize real multi-switching/shrinkage provider-grade instances (I-4).
2. Internalize default constructive structured-provider availability from those
   instances (I-2).
3. Internalize the bridge
   `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` and remove
   `hFormulaToPpoly` from final wrappers (I-5).

Minimal in-repo completion check:
- `./scripts/check.sh` passes.
- Final `P != NP` theorem family no longer requires external bridge arguments.

For full technical status, use `STATUS.md` and `AXIOMS_FINAL_LIST.md`.
