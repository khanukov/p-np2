# Frequently Asked Questions

## Q: What is the current formal result?

**A:** The active machine-checked result is a **conditional** formula-track
separation (`NP_not_subset_PpolyFormula`) in `pnp3/Magnification/FinalResult.lean`.

## Q: Are there active axioms or sorries in `pnp3/`?

**A:** No.

- Active `axiom` declarations: 0
- Active `sorry/admit`: 0

`./scripts/check.sh` enforces the axiom check.

## Q: Is I-1 (localized `PpolyReal -> PpolyFormula` bridge) closed?

**A:** Yes for the current interface.

- `trivialFormulaizer`
- `gapPartialMCSP_realization_trivial`

are implemented in `pnp3/ThirdPartyFacts/PpolyFormula.lean` and consumed by
bridge wrappers.

## Q: Is I-3 (`hCardHalf`) closed?

**A:** Closed at the certificate contract level.

- Low-level lemmas still have explicit `hCardHalf` parameters.
- Main constructive route has auto discharge through
  `HalfTableCertificateBound` and
  `locality_lift_partial_of_certificate_auto`.

## Q: What is still external?

**A:** Three areas remain:

1. I-2: default structured locality provider internalization.
2. I-5: bridge `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` for final
   `P != NP` wrappers.
3. Optional stronger bridge layers (kept explicit and separate).

## Q: Is NP encoded via arbitrary Lean verifiers?

**A:** No. The canonical interface is TM-faithful:

- `NP := NP_TM`
- `NP_strict := NP_TM`

For Partial-MCSP, NP evidence is carried by explicit TM witness packages
rather than verifier-function stubs.

## Q: Is `P != NP` already unconditional in this repository?

**A:** No. `P != NP` wrappers are conditional on an explicit bridge
`hFormulaToPpoly` in `FinalResult.lean`.

## Q: What should reviewers verify first?

**A:** Start with:

1. `STATUS.md`
2. `TODO.md`
3. `AXIOMS_FINAL_LIST.md`
4. `pnp3/Magnification/FinalResult.lean`
5. `pnp3/Tests/AxiomsAudit.lean`

## Q: Minimal reproducibility commands?

```bash
lake build
lake test
./scripts/check.sh
```
