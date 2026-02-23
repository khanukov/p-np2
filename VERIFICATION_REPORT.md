# Verification Report - Docs vs Code

**Generated:** 2026-02-23

## Summary

- Active `axiom` declarations in `pnp3/`: **0**
- Active `sorry`/`admit` in `pnp3/`: **0**
- `lake build`: pass
- `./scripts/check.sh`: pass
- Strategic proof target is fixed to `AC^0` lower-bound families.

## Key alignment updates applied

1. Documentation no longer treats the old localized bridge placeholder
   `GapPartialMCSPPpolyRealToPpolyFormulaGoal p` as an active dependency.
2. Locality-lift docs now reflect certificate auto-route
   (`HalfTableCertificateBound` / `..._of_certificate_auto`).
3. I-4 status is now explicit and unconditional in AC0 scope:
   - **Барьер I-4 (Multi-Switching и Locality Provider) ПОЛНОСТЬЮ И
     БЕЗУСЛОВНО ЗАКРЫТ конструктивным кодом для класса AC0 через модуль
     AC0LocalityBridge**.
4. Documentation now explicitly states the intentional scope boundary:
   - no global conversion `Ppoly -> AC0`,
   - hardness-magnification formalization is intentionally aimed at
     lower bounds against `AC^0` families.
5. Final-result docs track the new AC0 hooks:
   - `NP_not_subset_AC0_final*`
   - fixed-parameter `NP_not_subset_AC0_at_param*`
   - TM-witness bridge `strictGapNPFamily_of_tmWitnesses`.

## Remaining external inputs (outside AC0-core scope)

1. Non-AC0 wrapper bridge
   (`NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`) for unconditional
   `P != NP` wrappers.
2. Any global `PpolyFormula -> AC0` transport is intentionally out of scope
   and not required for the AC0-core claim.

## Scope note

This report validates documentation consistency with the current codebase.
It is not a claim of unconditional `P != NP` resolution over full `P/poly`.
