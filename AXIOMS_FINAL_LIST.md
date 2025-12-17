# Complete Axiom Inventory - P≠NP Formalization
## Official List for Publication

**Project**: Formal Proof Architecture for P≠NP in Lean 4
**Revision Date**: 2025-12-16
**Total Active Axioms (`pnp3/`)**: 5
**Complexity Interface Axioms**: 0 (replaced by imported theorems)

---

## Executive Summary

The current `pnp3/` proof development depends on five externally justified
statements.  They fall into two natural families:

| Category | Files | Axioms | Literature Anchor |
|----------|-------|--------|--------------------|
| Part A — Switching/Shrinkage | `ThirdPartyFacts/Facts_Switching.lean` | 2 | Håstad (1986), Williams (2014) |
| Part C — Anti-checker lower bounds | `LowerBounds/AntiChecker.lean` | 3 | Lipton–Young (1994), Chapman–Williams (2015), OPS (2019/2021) |

Every interface lemma in `pnp3/Complexity/Interfaces.lean` is now a theorem:
`P_subset_Ppoly_proof` and `P_ne_NP_of_nonuniform_separation` import concrete
proofs from the lightweight `Facts/PsubsetPpoly` package.

Archived copies of the older switching/magnification axioms remain in
`archive/` for historical reference but are not part of the active build. All
magnification triggers (`OPS_trigger_general`, `OPS_trigger_formulas`,
`Locality_trigger`, `CJW_sparse_trigger`) are fully proved in Lean.

---

## Detailed Catalogue

### Part A — Switching and Shrinkage (2 axioms)

1. **`partial_shrinkage_for_AC0`** — `pnp3/ThirdPartyFacts/Facts_Switching.lean`
   - Partial PDT certificate with explicit depth and error bounds.
   - Source: Håstad (1986), Servedio–Tan (2019).
2. **`shrinkage_for_localCircuit`** — same file, local-circuit variant.
   - Source: Williams (2014), Chen–Oliveira–Santhanam (2022).

### Part C — Anti-Checker Lower Bounds (3 axioms)

3. **`antiChecker_exists_large_Y`** — `pnp3/LowerBounds/AntiChecker.lean`
   - Base anti-checker: large family `Y` exceeding scenario capacity.
4. **`antiChecker_exists_large_Y_local`** — local solver version.
5. **`antiChecker_exists_testset_local`** — local solver + test set.
   - Sources for 3–5: Lipton–Young (1994), Chapman–Williams (2015),
     Oliveira–Pich–Santhanam (2019/2021).

✅ **PROVEN** in Part C:
- `antiChecker_exists_testset` (AC⁰ with test set), derived internally.
- `antiChecker_exists_large_Y_from_testset` (helper corollary).

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
- `magnification_AC0_MCSP` and `FCE_implies_MCSP`

They are excluded from the active build and from the totals above.

---

## Change Log

- **2025-12-17** — Marked `antiChecker_exists_large_Y` as a theorem (derived
  from the test-set axiom) and reduced the active axiom count to 5.
- **2025-12-16** — Synced documentation after re-verifying Part D: all
  magnification triggers remain proven, active axiom count stays at 6.
- **2025-10-25** — Historical update: totals moved to 6 axioms; marked
  `CJW_sparse_trigger` proven; clarified that all magnification triggers are
  theorems (superseded by the 5-axiom count above).
- **2025-10-24** — Updated totals to 7 axioms, marked `Locality_trigger` as
  proven, reclassified complexity interfaces as theorems, and documented
  retirement of depth-2 switching files.
