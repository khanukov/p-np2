# Critique of P≠NP Formalization Repository

## Overview

This repository (`pnp3`) aims to formalize a proof of $P \ne NP$ using the Partial MCSP problem and the Switching-Atlas Lemma (SAL). The codebase is a mix of Lean 4 verification and Python experiments.

## Key Findings

### 1. Conditional Results
The main theorem, `NP_not_subset_PpolyFormula_final` (in `pnp3/Magnification/FinalResult.lean`), is formally verified but **conditional**. It relies on a strong external hypothesis: `StructuredLocalityProviderPartial`.

*   **Assumption:** This hypothesis asserts that any Partial MCSP instance solvable by small formulas must admit a "locality witness" (restriction-based simplifier). This essentially assumes a property similar to the "Natural Proofs" barrier is overcome or circumvented by the problem structure.
*   **Implication:** The proof is valid *relative to* this provider, but does not prove $P \ne NP$ unconditionally without a construction for this provider.

### 2. Trivial Shrinkage Construction
A critical issue was identified in the shrinkage implementation (`pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean`).

*   **The Issue:** The theorem `shrinkage_depth2_cnf_family_of_bound` is used to provide shrinkage witnesses. While it correctly proves the existence of a "Good" restriction (one that simplifies the formula), the witness it constructs uses `partialCertificate_from_restriction_trivial`.
*   **Consequence:** This trivial construction returns a decision tree of depth $2^n$ (listing all satisfying assignments).
*   **Impact:** For complexity lower bounds, we need shrinkage to reduce depth to $O(n / n^\epsilon)$. A depth of $2^n$ is vacuous because any boolean function has a decision tree of depth $2^n$. The sophisticated machinery in `TraceBridge.lean` (which connects restrictions to small depth) is present but **unused** in the final bound.

### 3. Python Experiments (`experiments/`)
The `lemma_b_search.py` script is a prototype with significant limitations:

*   **Exponential Complexity:** It enumerates truth tables of size $2^n$, limiting its use to $n \le 4$.
*   **Ambiguous Counting:** `function_counts` aggregates circuit counts across all depths. This means a function computable at depth 2 is also counted at depth 3, 4, etc., distorting the "complexity" distribution.
*   **Code Quality:** Lack of type hints, potential double-counting logic errors, and absence of unit tests for the script itself.

### 4. Axiom Audit
The Lean proofs are free of `sorry` or `admit` in the `pnp3` directory. The "axiom audit" confirms dependencies only on standard axioms (`Classical.choice`, `propext`, etc.) and the explicit `Partial` interface assumptions.

## Recommendations

1.  **Fix Shrinkage:** The `shrinkage_depth2_cnf_family_of_bound` theorem should be updated to use `partialCertificate_from_good_restriction` (which uses `TraceBridge`) instead of the trivial version. This will require proving that the "Good" restriction property actually implies the depth bound in the specific `PartialCertificate` structure used.
2.  **Clarify Hypotheses:** The `StructuredLocalityProviderPartial` should be clearly documented as the central unproven assumption (or "conjecture") of the repository in `README.md`.
3.  **Optimize Python:** The enumeration script should be rewritten to use a more efficient representation (e.g., bitwise operations on numpy arrays or a C++ extension) if larger $n$ is desired. The counting logic should be fixed to count *minimal* circuit size.
