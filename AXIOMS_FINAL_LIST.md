# Complete Axiom Inventory - P≠NP Formalization
## Official List for Publication

**Project**: Formal Proof Architecture for P≠NP in Lean 4  
**Revision Date**: 2026-02-19  
**Total Active Axioms (`pnp3/`)**: 1  
**Complexity Interface Axioms**: 0

---

## Executive Summary

The active `pnp3/` tree currently has exactly one project-specific axiom:

- `ThirdPartyFacts.localizedFamilyWitness_partial`
  (`pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`)

From `#print axioms` audits (`pnp3/Tests/AxiomsAudit.lean`):

- `P_ne_NP_final` and `P_ne_NP_final_asymptotic` depend on
  `[propext, Classical.choice, Quot.sound, ThirdPartyFacts.localizedFamilyWitness_partial]`.
- Core bridge and lower-bound nodes in the same chain depend only on
  `[propext, Classical.choice, Quot.sound]`.

So the only project-specific external gap on the final theorem cone is
`localizedFamilyWitness_partial`.

---

## Detailed Catalogue

### Explicit Axioms (`pnp3/`)

- **`localizedFamilyWitness_partial`** — `pnp3/ThirdPartyFacts/LocalizedWitness_Partial.lean`
  - Axiom: centralized scaffold for `LocalizedFamilyWitnessHypothesis_partial`
    used by the partial general→local magnification bridge.

### External Witness Interfaces (non-axiom theorems)

- `ThirdPartyFacts.partial_shrinkage_for_AC0`
- `ThirdPartyFacts.shrinkage_for_localCircuit`

Both are theorems requiring external witness objects (`FamilyIsAC0` /
`FamilyIsLocalCircuit`), tracked separately from explicit axioms.

### Complexity Interfaces

- `P_subset_Ppoly_proof` and `P_ne_NP_of_nonuniform_separation` are proven
  theorems (not axioms).
- `Facts/PsubsetPpoly` now uses a non-trivial `Ppoly` witness interface:
  `InPpoly` includes a polynomial bound and a polynomial-time evaluator for the
  family predicate.

---

## Archived Axioms

Historical axioms remain only under `archive/` and are excluded from active
builds and totals.
