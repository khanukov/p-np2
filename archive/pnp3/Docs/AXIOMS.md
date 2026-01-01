# External Axioms in P≠NP Formalization
## Complete Reference List

Last updated: 2025-12-26

---

## Overview

After the latest cleanup the active `pnp3/` tree contains **4 explicit
placeholder axioms** (all confined to the multi-switching encoding scaffold).
The pipeline uses shrinkage theorems that are *parameterised* by explicit
witnesses, so the logic remains fully formal while the data are supplied via
the hypotheses. They are grouped along the analytical steps of the pipeline:

- **Part A (Switching / Shrinkage)**: 0 axioms
- **Part A' (Multi-switching encoding placeholders)**: 4 axioms (temporary)
- **Part C (Anti-Checker lower bounds)**: 0 axioms — all results are theorems
- **Part D (Magnification triggers / bridges)**: 0 axioms
- **Complexity interfaces**: 0 axioms — `P ⊆ P/poly` is imported from the
  lightweight `Facts/PsubsetPpoly` package, while `P ≠ NP` is derived in
  `Complexity/Interfaces.lean` from `P_subset_Ppoly` and `NP_not_subset_Ppoly`.

All references below point to the current source files under `pnp3/`.
Legacy axioms that lived in `Core/ShrinkageAC0.lean` and
`ThirdPartyFacts/Depth2_Switching_Spec.lean` have been archived; see the final
section for details.

---

## Part A: Switching Lemma / Shrinkage

### A.1: `partial_shrinkage_for_AC0`

**Location**: `pnp3/ThirdPartyFacts/Facts_Switching.lean` (see `partial_shrinkage_for_AC0`)

**Statement (theorem)**:
```lean
theorem partial_shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2)
```

**Role**: Håstad-style switching lemma delivering a partial PDT certificate with
explicit depth and error bounds. The hypothesis `hF` packages a concrete
`AC0CircuitWitness`, so the lemma is a theorem with explicit input data
(otherwise the statement would be false, e.g. for PARITY).

**Literature**: Håstad (1986), Servedio–Tan (2019).

---

### A.2: `shrinkage_for_localCircuit`

**Location**: `pnp3/ThirdPartyFacts/Facts_Switching.lean` (see `shrinkage_for_localCircuit`)

**Statement (theorem)**:
```lean
theorem shrinkage_for_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n)
    (hF : FamilyIsLocalCircuit params F) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2)
```

**Role**: Local-circuit variant of the switching lemma. The hypothesis `hF`
packages a concrete `LocalCircuitWitness` (see `Facts_Switching`), so the lemma
is a theorem whose data are supplied via the hypothesis rather than an axiom.

**Literature**: Williams (2014), Chen–Oliveira–Santhanam (2022).

---

## Part C: Anti-Checker Lower Bounds

### C.1 (proved): `antiChecker_exists_large_Y`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:137`

**Status**: **Theorem.** Base anti-checker existence (large family `Y`) is now
derived internally via `noSmallAC0Solver` and the capacity gap bounds.

### C.2 (proved): `antiChecker_exists_testset`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:158`

**Status**: **Theorem.** Test-set refinement derived internally from the
proved C.1.

### C.3 (proved): `antiChecker_exists_large_Y_local`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:283`

**Summary**: Local-circuit analogue of C.1 tailored to the locality budget.

**Status**: **Theorem.** Derived internally via the new `noSmallLocalCircuitSolver`
contradiction and capacity-gap bounds.

### C.4 (proved): `antiChecker_exists_testset_local`

**Location**: `pnp3/LowerBounds/AntiChecker.lean:349`

**Status**: **Theorem.** Derived from C.3 via the capacity contradiction (no
additional axioms).

**Summary**: Local version of the test-set refinement.

**Literature for C.1–C.4**: Lipton–Young (1994), Chapman–Williams (2015),
Oliveira–Pich–Santhanam (2019/2021).

---

## Part D: Magnification Bridges & Numeric Bridges

All trigger theorems in this section remain **proved**.  There are currently
no external axioms associated with the magnification interfaces.

---

## Part A': Multi-switching encoding (placeholders)

These axioms are **temporary stubs** used to keep the multi-switching API
stable while the canonical trace encoding is developed. They are isolated to
`pnp3/AC0/MultiSwitching/Encoding.lean` and do not participate in the current
`P_ne_NP_final` derivation.

- `BadTraceEvent` — placeholder predicate for the CNF canonical trace notion of badness.
- `defaultCCDTAlgorithm` — placeholder CCDT algorithm for CNF families.
- `canonicalTraceEncoding_witness` — placeholder encoding witness into `R_{s-t} × Aux`.
- `exists_good_restriction_of_canonical_trace_encoding` — placeholder existence lemma.

---

## Models: Proven Facts

### M.1 (proved): `gapMCSP_in_NP`

**Location**: `pnp3/Models/Model_GapMCSP.lean`

**Summary**: `GapMCSP ∈ NP` for fixed parameters `p`.  Верификатор задан
невычислимо через прямую проверку существования схемы размера ≤ `sYES`,
что эквивалентно полному перебору входов и сравнению `Circuit.eval` с
`truthTableFunction`.  Сертификат имеет квадратичную длину
`certificateLength n 2 = n^2 + 2`, а временной бюджет фиксируется как
`(n + certificateLength n 2)^2 + 2`.  Новых аксиом не добавлено.

### D.1: `OPS_trigger_general`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:74`

**Summary**: Abstract OPS trigger converting a general lower-bound hypothesis
into `NP_not_subset_Ppoly`.  Расширенный конспект и исторический план снятия
аксиомы см. в `pnp3/Docs/OPS_trigger_general.md`.

### D.2: `OPS_trigger_formulas`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:82`

**Summary**: Formula-specific OPS trigger yielding `NP_not_subset_Ppoly` from an
`N^{2+δ}` lower bound.  Реализован как частный случай `OPS_trigger_general`
через подстановку `statement := ∀ _ : SmallAC0Solver p, False`; текстовое
обоснование см. в `pnp3/Docs/OPS_trigger_formulas.md`.

### D.3: `Locality_trigger`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:90`

**Summary**: Locality barrier implying `NP_not_subset_Ppoly` from a
`N·(log N)^κ` lower bound for local circuits.  ✅ Fully proved via
contraposition (locality lift + anti-checker), replacing the former axiom.

### D.4: `CJW_sparse_trigger`

**Location**: `pnp3/Magnification/Facts_Magnification.lean:95`

**Summary**: Sparse-language trigger (CJW) showing that super-linear sparse
lower bounds magnify to `NP_not_subset_Ppoly`. ✅ **PROVEN** via конструктивный
перебор положительных примеров (см. `defaultSparseSolver`).

**Literature for D.1–D.4**: Oliveira–Pich–Santhanam (2019), Chapman–Jansen–Williams (2022).

---

## Complexity Interfaces (Proven Facts)

The interface file `pnp3/Complexity/Interfaces.lean` no longer declares axioms.
The inclusion `P ⊆ P/poly` is imported from the self-contained package
`Facts/PsubsetPpoly`, while the classical implication to `P ≠ NP` is proved
locally from `NP_not_subset_Ppoly` and `P_subset_Ppoly`.

- `@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly`
  - Witness of the inclusion `P ⊆ P/poly`.  Source:
    `Facts/PsubsetPpoly/Proof/Complexity/PsubsetPpoly.lean`.
- `theorem P_ne_NP_of_nonuniform_separation`
  - Classical deduction `NP_not_subset_Ppoly → P_subset_Ppoly → P_ne_NP`
    packaged inside the interface.

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
