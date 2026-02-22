# Final Axiom Analysis (PNP3)

**Updated:** 2026-02-22

## Active counts

- Active `axiom` in `pnp3/`: **0**
- Active `sorry`/`admit` in `pnp3/`: **0**

## Remaining external dependencies (non-axiomatic)

1. Witness-backed multi-switching/shrinkage inputs for target solver families.
2. Formula-certificate provider package availability for default constructive
   locality-provider wiring (`FormulaCertificateProviderPartial`).
3. Final bridge `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`
   (`hFormulaToPpoly`) for `P != NP` wrappers.

## Corrections vs older docs

- Localized bridge placeholder
  `GapPartialMCSPPpolyRealToPpolyFormulaGoal p` is no longer active.
- `hCardHalf` is no longer a manual argument in the main certificate route;
  automation is provided through certificate contracts/typeclass export.

## Conclusion

The tree is axiom-clean, but the full constructive closure is still conditional
on explicit external witness/provider/bridge inputs listed above.
