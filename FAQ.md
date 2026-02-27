# Frequently Asked Questions

## Q: What is the current formal result?

**A:** The active machine-checked target is the semantic AC0-focused
formula-separation route in `pnp3/Magnification/FinalResult.lean`, with hooks:

- fixed-parameter semantic hooks:
  `NP_not_subset_PpolyFormula_from_params_semantic`,
  `NP_not_subset_PpolyFormula_from_params_semantic_of_syntacticEasy`
- asymptotic semantic hooks:
  `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic`,
  `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic_of_syntacticEasy`
- final wrappers:
  `NP_not_subset_PpolyFormula_final`,
  `P_ne_NP_final`

Interpretation note:
names containing `...PpolyFormula_final...` in the same module are route-level
formula-separation wrappers for the AC0 pipeline, not standalone global
non-uniform separation claims.

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

**A:** Main remaining external area:

1. I-5: bridge `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly` for final
   `P != NP` wrappers.
2. Optional stronger bridge layers (kept explicit and separate).

I-2 note:
- Provider-default wiring is already closed constructively in a contract-scoped
  way (`..._of_multiswitching_contract` route in `FinalResult.lean` and
  `LocalityProvider_Partial.lean`).

## Q: Is NP encoded via arbitrary Lean verifiers?

**A:** No. The canonical interface is TM-faithful:

- `NP := NP_TM`
- `NP_strict := NP_TM`

For Partial-MCSP, NP evidence is carried by explicit TM witness packages
rather than verifier-function stubs.

## Q: Is `P != NP` already unconditional in this repository?

**A:** No. `P != NP` wrappers are conditional on an explicit bridge
`hFormulaToPpoly` in `FinalResult.lean`.

## Q: Is a global conversion `PpolyFormula -> AC0` claimed?

**A:** No. This repository intentionally does not make that claim; the active
formalization is scoped to AC0-target lower-bound routes.

## Q: What should reviewers verify first?

**A:** Start with:

1. `STATUS.md`
2. `TODO.md`
3. `AXIOMS_FINAL_LIST.md`
4. `pnp3/Magnification/FinalResult.lean`
5. `pnp3/Tests/AxiomsAudit.lean`

## Q: What is the most constructive entrypoint right now?

**A:** Prefer semantic/syntactic-easy routes:

1. Fixed parameter `p`:
   `NP_not_subset_PpolyFormula_from_params_semantic_of_syntacticEasy`.
2. Asymptotic/family route:
   `NP_not_subset_PpolyFormula_of_asymptotic_hypothesis_semantic_of_syntacticEasy`.

## Q: Minimal reproducibility commands?

```bash
lake build
lake test
./scripts/check.sh
```
