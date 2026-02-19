# Complete Axiom Inventory - P≠NP Formalization
## Official List for Publication

**Project**: Formal Proof Architecture for P≠NP in Lean 4
**Revision Date**: 2025-12-26
**Total Active Axioms (`pnp3/`)**: 3
**Complexity Interface Axioms**: 0 (replaced by imported theorems)

---

## Executive Summary

The active `pnp3/` proof development uses two external NP‑hardness axioms
and one explicit localized-witness scaffold axiom for the partial
general→local bridge. All other former placeholders have been moved to the
`archive/` tree and are no longer part of the active build.

The archived multi-switching placeholders are kept out of the active
`pnp3/` build and therefore do **not** participate in the final
`P_ne_NP_final` derivation.

| Category | Files | Axioms | Literature Anchor |
|----------|-------|--------|--------------------|
| Part A — Switching/Shrinkage | `ThirdPartyFacts/Facts_Switching.lean` | 0 | Håstad (1986), Williams (2014) |
| Partial MCSP NP-hardness | `ThirdPartyFacts/Hirahara2022.lean` | 2 | Hirahara (FOCS 2022) |
| Partial localized witness scaffold | `ThirdPartyFacts/LocalizedWitness_Partial.lean` | 1 | repository-local interface gap |

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

### Part A' — Multi-switching encoding (archived placeholders)

The canonical trace encoding stubs have been moved to
`archive/pnp3/AC0/MultiSwitching/Encoding_CanonicalTrace_Placeholders.lean`.
They are not part of the active `pnp3/` build.

### Partial MCSP — NP-hardness (external, active)

- **`PartialMCSP_profile_is_NP_Hard_rpoly`** — `pnp3/ThirdPartyFacts/Hirahara2022.lean`
- **`PartialMCSP_is_NP_Hard`** — `pnp3/ThirdPartyFacts/Hirahara2022.lean`
  - Axiom: Partial MCSP NP-hardness (logical reductions).
  - Source: Hirahara (FOCS 2022).

### Partial MCSP — localized witness scaffold (external, active)

- **`localizedFamilyWitness_partial`** — `pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`
  - Axiom: centralized scaffold for `LocalizedFamilyWitnessHypothesis_partial`
    used by the partial general→local magnification bridge.
  - Status: explicitly tracked temporary gap for constructive discharge.

### Part C — Anti-Checker Lower Bounds (0 axioms)

✅ **PROVEN** in Part C (all anti-checker results are theorems):
- `antiChecker_exists_large_Y` (AC⁰ large-Y), derived internally.
- `antiChecker_exists_testset` (AC⁰ with test set), derived internally.
- `antiChecker_exists_large_Y_from_testset` (helper corollary).
- `antiChecker_exists_testset_local` (local test-set refinement) and
  `antiChecker_exists_large_Y_local_from_testset`.
- `antiChecker_exists_large_Y_local` (local-circuit base statement).

### Part D — Magnification Bridges (all proved)

- **`OPS_trigger_general_contra_partial` / `OPS_trigger_formulas_partial`** —
  `pnp3/Magnification/Facts_Magnification_Partial.lean`
  - ✅ **PROVEN**: general OPS trigger (lower-bound hypothesis ⇒ `NP_not_subset_Ppoly`).
- `OPS_trigger_formulas_partial` is proved constructively from the same general-contrapositive layer.
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

- **2026-02-19** — Re-audited active tree: two NP-hardness axioms in
  `ThirdPartyFacts/Hirahara2022.lean` plus one localized-witness scaffold axiom
  in `ThirdPartyFacts/LocalizedWitness_Partial.lean`; documentation synchronized.
- **2025-12-27** — Confirmed locality-lift and magnification bridges are fully
  proved in Lean.
- **2025-12-16** — Synced documentation after re-verifying Part D: all
  magnification triggers remain proven.
- **2025-10-25** — Historical update: interface axioms replaced by theorems and
  magnification triggers proven.
