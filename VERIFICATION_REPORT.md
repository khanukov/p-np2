# Verification Report - Docs vs Code

**Generated:** 2026-02-22

## Summary

- Active `axiom` declarations in `pnp3/`: **0**
- Active `sorry`/`admit` in `pnp3/`: **0**
- `lake build`: pass
- `./scripts/check.sh`: pass

## Key alignment updates applied

1. Documentation no longer treats the old localized bridge placeholder
   `GapPartialMCSPPpolyRealToPpolyFormulaGoal p` as an active dependency.
2. Locality-lift docs now reflect certificate auto-route
   (`HalfTableCertificateBound` / `..._of_certificate_auto`).
3. Final-result docs now consistently distinguish:
   - conditional active formula-track separation,
   - conditional `P != NP` wrappers requiring `hFormulaToPpoly`.

## Remaining external inputs (non-axiomatic)

1. Real multi-switching/shrinkage witness/provider instances (I-4).
2. Default constructive locality-provider internalization via those instances (I-2).
3. Formula-to-`P/poly` bridge for unconditional `P != NP` wrapper closure (I-5).

## Scope note

This report validates documentation consistency with the current codebase.
It is not a claim of unconditional `P != NP` resolution.
