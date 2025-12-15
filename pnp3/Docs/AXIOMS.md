# External Axioms in P≠NP Formalization
## Complete Reference List

Last updated: 2025-10-24

---

## Overview

After the October cleanup the active `pnp3/` tree contains **10 external axioms**.
They are grouped exactly along the three analytical steps of the pipeline:

- **Part A (Switching / Shrinkage)**: 2 axioms
- **Part C (Anti-Checker lower bounds)**: 4 axioms
- **Part D (Magnification triggers)**: 4 axioms
- **Complexity interfaces**: 0 axioms — `P ⊆ P/poly` and `P ≠ NP` are now
  imported as proven theorems from the lightweight `Facts/PsubsetPpoly` package.

All references below point to the current source files under `pnp3/`.
Legacy axioms that lived in `Core/ShrinkageAC0.lean` and
`ThirdPartyFacts/Depth2_Switching_Spec.lean` have been archived; see the final
section for details.

---

## Part A: Switching Lemma / Shrinkage

### A.1: `partial_shrinkage_for_AC0`

**Location**: `pnp3/ThirdPartyFacts/Facts_Switching.lean:119`

**Statement**:
```lean
axiom partial_shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2)
```

**Role**: Håstad-style switching lemma delivering a partial PDT certificate with
explicit depth and error bounds. Required for the combinatorial part of the
pipeline.

**Literature**: Håstad (1986), Servedio–Tan (2019).

---

### A.2: `shrinkage_for_localCircuit`

**Location**: `pnp3/ThirdPartyFacts/Facts_Switching.lean:278`

**Statement**:
```lean
axiom shrinkage_for_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n) :
    ∃ (C : Core.CommonPDT params.n F),
      Core.depthBound C ≤ params.M + 1 ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2)
```

**Role**: Local-circuit variant of the switching lemma, used when the solver is
restricted by a locality parameter.

**Literature**: Williams (2014), Chen–Oliveira–Santhanam (2022).

---

## Part C: Anti-Checker Lower Bounds

### C.1: `antiChecker_exists_large_Y`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:171`

**Summary**: Guarantees an exponential-size indistinguishable set `Y` against
small AC⁰ solvers, packaged as a family inside the SAL framework.

### C.2: `antiChecker_exists_testset`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:237`

**Summary**: Strengthens C.1 by producing a small test set witnessing the
indistinguishability of functions in `Y`.

### C.3: `antiChecker_exists_large_Y_local`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:305`

**Summary**: Local-circuit analogue of C.1 tailored to the locality budget.

### C.4: `antiChecker_exists_testset_local`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:371`

**Summary**: Local version of the test-set refinement.

**Literature for C.1–C.4**: Lipton–Young (1994), Chapman–Williams (2015),
Oliveira–Pich–Santhanam (2019/2021).

---

## Part D: Magnification Bridges

### D.1: `OPS_trigger_general`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:74`

**Summary**: Abstract OPS trigger converting a general lower-bound hypothesis
into `NP_not_subset_Ppoly`.

### D.2: `OPS_trigger_formulas`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:82`

**Summary**: Formula-specific OPS trigger yielding `NP_not_subset_Ppoly` from an
`N^{2+δ}` lower bound.  Реализован как частный случай `OPS_trigger_general`
через подстановку `statement := ∀ _ : SmallAC0Solver p, False`; текстовое
обоснование см. в `pnp3/Docs/OPS_trigger_formulas.md`.

### D.3: `Locality_trigger`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:90`

**Summary**: Locality barrier implying `NP_not_subset_Ppoly` from a
`N·(log N)^κ` lower bound for local circuits.

### D.4: `CJW_sparse_trigger`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:95`

**Summary**: Sparse-language trigger (CJW) showing that super-linear sparse
lower bounds magnify to `NP_not_subset_Ppoly`.

**Literature for D.1–D.4**: Oliveira–Pich–Santhanam (2019), Chapman–Jansen–Williams (2022).

---

## Complexity Interfaces (Proven Facts)

The interface file `pnp3/Complexity/Interfaces.lean` no longer declares axioms.
Both statements listed below are bona fide theorems imported from the
self-contained package `Facts/PsubsetPpoly`.

- `@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly`
  - Witness of the inclusion `P ⊆ P/poly`.  Source:
    `Facts/PsubsetPpoly/Proof/Complexity/PsubsetPpoly.lean`.
- `theorem P_ne_NP_of_nonuniform_separation`
  - Classical deduction `NP_not_subset_Ppoly → P_subset_Ppoly → P_ne_NP`.

---

## Archived or Retired Axioms

The following declarations used to live in the active tree but are now archived
under `archive/`:

- `partial_shrinkage_with_oracles`
- `depth2_switching_probabilistic`
- `depth2_constructive_switching`
- Duplicate interfaces for `P_subset_Ppoly`
- Magnification bridge axioms in `old_attempts/OldAttempts/NP_separation.lean`

They remain documented for historical context but do not contribute to the
current proof graph.
