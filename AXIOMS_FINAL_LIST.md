# Complete Axiom Inventory - P≠NP Formalization
## Official List for Publication

**Project**: Formal Proof Architecture for P≠NP in Lean 4
**Revision Date**: 2025-12-26
**Total Active Axioms (`pnp3/`)**: 4
**Complexity Interface Axioms**: 0 (replaced by imported theorems)

---

## Executive Summary

The current `pnp3/` proof development depends on two shrinkage theorems that
still require externally supplied witnesses, and it also contains a small set
of **explicit placeholder axioms** for the in-progress multi-switching
canonical trace encoding. These placeholders are isolated to
`AC0/MultiSwitching/Encoding.lean` and do **not** participate in the final
`P_ne_NP_final` derivation at present.

| Category | Files | Axioms | Literature Anchor |
|----------|-------|--------|--------------------|
| Part A — Switching/Shrinkage | `ThirdPartyFacts/Facts_Switching.lean` | 0 | Håstad (1986), Williams (2014) |
| Part A' — Multi-switching encoding (placeholder) | `AC0/MultiSwitching/Encoding.lean` | 4 | In-progress (canonical trace encoding) |

Every interface lemma in `pnp3/Complexity/Interfaces.lean` is now a theorem:
`P_subset_Ppoly_proof` and `P_ne_NP_of_nonuniform_separation` import concrete
proofs from the lightweight `Facts/PsubsetPpoly` package.

Archived copies of the older switching/magnification axioms remain in
`archive/` for historical reference but are not part of the active build. All
magnification triggers (`OPS_trigger_general`, `OPS_trigger_formulas`,
`Locality_trigger`, `CJW_sparse_trigger`) are fully proved in Lean.

---

## Detailed Catalogue

### Part A — Switching and Shrinkage (external witnesses)

- **`partial_shrinkage_for_AC0`** — `pnp3/ThirdPartyFacts/Facts_Switching.lean`
  - Theorem, but requires an external `AC0CircuitWitness` via `FamilyIsAC0`.
  - Source: Håstad (1986), Servedio–Tan (2019).
- **`shrinkage_for_localCircuit`** — same file, local-circuit variant.
  - Theorem, but requires an external `LocalCircuitWitness` via `FamilyIsLocalCircuit`.
  - Source: Williams (2014), Chen–Oliveira–Santhanam (2022).

### Part A' — Multi-switching encoding (placeholders)

These axioms are **temporary stubs** for the canonical trace encoding.
They live in `pnp3/AC0/MultiSwitching/Encoding.lean` and must be replaced
by constructive definitions/lemmas as the canonical encoding is finalized.

- **`BadTraceEvent`** — placeholder predicate for the CNF canonical trace notion of badness.
- **`defaultCCDTAlgorithm`** — placeholder CCDT algorithm for CNF families.
- **`canonicalTraceEncoding_witness`** — placeholder encoding witness into `R_{s-t} × Aux`.
- **`exists_good_restriction_of_canonical_trace_encoding`** — placeholder existence lemma.

### Part C — Anti-Checker Lower Bounds (0 axioms)

✅ **PROVEN** in Part C (all anti-checker results are theorems):
- `antiChecker_exists_large_Y` (AC⁰ large-Y), derived internally.
- `antiChecker_exists_testset` (AC⁰ with test set), derived internally.
- `antiChecker_exists_large_Y_from_testset` (helper corollary).
- `antiChecker_exists_testset_local` (local test-set refinement) and
  `antiChecker_exists_large_Y_local_from_testset`.
- `antiChecker_exists_large_Y_local` (local-circuit base statement).

### Part D — Magnification Bridges (all proved)

- **`OPS_trigger_general`** — `pnp3/Magnification/Facts_Magnification.lean`
  - ✅ **PROVEN**: general OPS trigger (lower-bound hypothesis ⇒ `NP_not_subset_Ppoly`).
- **`OPS_trigger_formulas`** — proved as a corollary of `OPS_trigger_general` for AC⁰ solvers.
- **`Locality_trigger`** — same file
  - ✅ **PROVEN**: locality barrier (`N·(log N)^κ`) established via constructive contraposition.
- **`CJW_sparse_trigger`** — same file
  - ✅ **PROVEN**: CJW sparse-language trigger via explicit sparse solver witness.
  - Sources: Oliveira–Pich–Santhanam (2019), Chapman–Jansen–Williams (2022).

---

## Complexity Interfaces (Proven)

- `@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly`
- `theorem P_ne_NP_of_nonuniform_separation`

Both results are imported from `Facts/PsubsetPpoly` and carry full Lean proofs.
They replace the earlier axioms `P_subset_Ppoly` and
`P_ne_NP_of_nonuniform_separation` that existed in historical branches.

---

## Archived Axioms

Legacy files kept under `archive/` still mention the following axioms:

- `partial_shrinkage_with_oracles`
- `depth2_switching_probabilistic`
- `depth2_constructive_switching`
- Duplicate `P_subset_Ppoly` declarations in `ComplexityClasses.lean`

They are excluded from the active build and from the totals above.

---

## Change Log

- **2025-12-26** — Added explicit placeholder axioms for multi-switching
  canonical trace encoding (4 total), and reclassified A.1/A.2 as theorems
  with external witnesses.
- **2025-12-18** — Marked `antiChecker_exists_large_Y` as a theorem (derived
  from the capacity-gap contradiction), reducing the active axiom count to 2.
- **2025-12-16** — Synced documentation after re-verifying Part D: all
  magnification triggers remain proven, active axiom count stays at 6.
- **2025-10-25** — Historical update: totals moved to 6 axioms; marked
  `CJW_sparse_trigger` proven; clarified that all magnification triggers are
  theorems (superseded by the 5-axiom count above).
- **2025-10-24** — Updated totals to 7 axioms, marked `Locality_trigger` as
  proven, reclassified complexity interfaces as theorems, and documented
  retirement of depth-2 switching files.
