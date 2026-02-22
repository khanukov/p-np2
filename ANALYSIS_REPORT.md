# Analysis Report: Conditional Nature of NP vs P/poly Proof (PNP3)

## Executive Summary

The proof of $NP \not\subseteq P/poly$ in this repository is currently **conditional**. The codebase is syntactically correct and free of `sorry` or `axiom` declarations within the `pnp3/` directory, meaning all defined theorems are rigorously proven relative to their premises. However, the main theorem `NP_not_subset_PpolyFormula_final` depends on a premise (`FormulaCertificateProviderPartial`) that has not been constructed for the target function class.

## Current Proof Status

*   **Main Theorem:** `NP_not_subset_PpolyFormula_final` (in `pnp3/Magnification/FinalResult.lean`) proves that $NP \not\subseteq P/poly$ (Formula-size version) **IF** provided with a `StructuredLocalityProviderPartial` witness.
*   **Missing Witness:** The witness `FormulaCertificateProviderPartial` (in `pnp3/Magnification/LocalityProvider_Partial.lean`) is required. This interface demands a function that takes any formula circuit solving the `gapPartialMCSP` language and produces a `ShrinkageCertificate` (proving the formula simplifies under random restrictions).
*   **Gap:** While the machinery to convert a "Good Family" of formulas into a `ShrinkageCertificate` exists (`pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean`), there is no proof that the formulas arising from the reduction actually form a "Good Family". This missing proof is essentially **Håstad's Switching Lemma** applied to the specific formulas in question.

## Analysis of Potential Issues

### 1. "False Assertions" check
There are no false assertions in the form of incorrect theorems derived from axioms or `sorry`.
*   **Axiom Audit:** A `grep` check confirms zero active axioms in `pnp3/`. The `ac0_formula_locality` axiom was correctly removed (see `pnp3/AC0/MultiSwitching/FullSwitching.lean`) as it was factually incorrect.
*   **Sorry Audit:** A `grep` check confirms zero `sorry` usages in `pnp3/`.

### 2. Trivial Constructions
The file `pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean` contains a `partialCertificate_from_restriction_trivial` theorem.
*   This constructs a decision tree of depth $2^n$ (exponential).
*   This satisfies the type signature of a `ShrinkageCertificate` but fails the quantitative requirements for the lower bound contradiction (which requires sub-linear dependency, e.g., $n/2$).
*   **Conclusion:** This is a valid placeholder for type-checking but useless for the final proof without a better construction (which requires the Switching Lemma).

## Roadmap to Completion

To complete the unconditional proof, the following steps are required (corresponding to item I-4 in `STATUS.md`):

1.  **Implement the Switching Lemma:** Formally prove that for the specific class of formulas (likely $AC^0$ or similar small-depth circuits) arising from the `gapPartialMCSP` reduction, a random restriction simplifies them to a decision tree of small depth (polylogarithmic or $n^\epsilon$) with high probability.
2.  **Construct `GoodFamilyCNF` Witness:** Use the Switching Lemma to prove that the family of formulas is a `GoodFamilyCNF`.
3.  **Implement `FormulaCertificateProviderPartial`:** Use `shrinkage_from_good_restriction` (in `ShrinkageFromGood.lean`) to convert the `GoodFamilyCNF` witness into the required `ShrinkageCertificate`.
4.  **Link to Main Theorem:** Pass this provider to `NP_not_subset_PpolyFormula_final`.

## Conclusion

The proof infrastructure (Magnification, Anti-Checker, Reduction) is complete. The combinatorial core (Switching Lemma application) is the sole missing piece preventing an unconditional result.
