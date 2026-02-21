# Plan to Fix P≠NP Formalization Semantics

This plan addresses the critical semantic gaps and "vacuous" proofs identified in the `pnp3` repository.

## Phase 1: Sanity & Interface Semantics

**Goal:** Ensure that the definitions of "Solver", "Circuit", and "Complexity Class" match standard theory and prevent trivial proofs.

1.  **Strict Solver Interface**
    *   **Task:** Modify `SmallAC0Solver_Partial` and `SmallLocalCircuitSolver_Partial` in `pnp3/LowerBounds/AntiChecker_Partial.lean`.
    *   **Action:** Ensure `decide` is not just a field but is tightly coupled with `correct`. (Already verified as present, but ensure `decide` is used in the Anti-Checker logic directly, avoiding "black box" parameters).
    *   **Check:** Verify that `params` alone are not sufficient to instantiate a solver.

2.  **Sanity Theorems**
    *   **Task:** Create `pnp3/Tests/SanityChecks.lean`.
    *   **Theorems:**
        *   `finite_language_in_P`: Prove that any language defined on a finite set of inputs (or with finite support) is in `P`.
        *   `Ppoly_nontrivial`: Prove `∃ L, L ∉ Ppoly` (using counting arguments).
        *   `n_equals_1_no_separation`: Prove that `P` and `NP` restricted to input length $n=1$ are indistinguishable without asymptotic context.

3.  **Strict Shrinkage Interface**
    *   **Task:** Modify `pnp3/ThirdPartyFacts/Facts_Switching.lean`.
    *   **Action:**
        *   Remove `M^2` from `ac0DepthBound_strong`. Define `ac0DepthBound_strong` purely as the polylogarithmic bound.
        *   This will break `ac0DepthBoundWitness_of_weak`. *This is intended.* It forces the proof to rely on a real polylog construction (currently missing or conditional).
    *   **Impact:** This converts the "vacuous strong theorem" into an honest "unproven goal".

## Phase 2: Logic Repair (Anti-Checker)

**Goal:** Remove "Ex Falso" witness generation.

1.  **Direct Negation**
    *   **Task:** Rewrite `antiChecker_exists_testset_partial` in `pnp3/LowerBounds/AntiChecker_Partial.lean`.
    *   **Action:** Instead of returning `∃ (T ...)` from `False.elim`, the theorem should conclude `¬ SmallAC0Solver_Partial`.
    *   **Refactor:** If `T` is needed for *subsequent* steps (Magnification), those steps must be refactored to accept "Absence of Solver" or `T` must be constructed *without* assuming the solver exists (which is the point of the Anti-Checker: it builds `T` to *defeat* the solver).
    *   **Correction:** The Anti-Checker should construct `T` *unconditionally* (or based on the *class* of circuits), and then prove `∀ C ∈ Class, C fails on T`.

## Phase 3: Asymptotic Final Result

**Goal:** Remove the `n=8` trivialization.

1.  **Asymptotic Parameters**
    *   **Task:** Modify `pnp3/Models/Model_PartialMCSP.lean` and `FinalResult.lean`.
    *   **Action:**
        *   Change `GapPartialMCSPParams` to be a function of `n`: `def params (n : Nat) : GapPartialMCSPParams`.
        *   Update `P_ne_NP_final` to quantify over `n`: `∀ k, ∃ n > k, ...` (standard separation).
    *   **Impact:** This will likely break the proof of `P_ne_NP_final` because the current witness `n=8` will no longer suffice. This exposes the true gap in the proof.

## Phase 4: Constructive Shrinkage (Long Term)

**Goal:** Implement the missing polylog shrinkage.

1.  **Connect TraceBridge**
    *   **Task:** In `pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean`, replace `partialCertificate_from_restriction_trivial` with a construction that uses `TraceBridge.lean`.
    *   **Action:**
        *   Prove that a "Good" restriction implies the existence of a small-depth decision tree (using `TraceBridge`).
        *   Construct `PartialCertificate` using this small tree.

## Execution Order

1.  **Phase 1 (Sanity)** is the highest priority to confirm the validity of the critique.
2.  **Phase 2 (Logic)** cleans up the misleading "constructive" claims.
3.  **Phase 3 (Asymptotics)** aligns the result with actual Complexity Theory.
