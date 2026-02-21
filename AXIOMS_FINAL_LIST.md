# Complete Axiom Inventory - PNP3 Formalization
## Official List for Publication

**Project**: Formal proof architecture for the PNP3 partial pipeline in Lean 4
**Revision Date**: 2026-02-20
**Total Active Axioms (`pnp3/`)**: 0
**Complexity Interface Axioms**: 0

---

## Executive Summary

The active `pnp3/` tree contains no global `axiom` declarations.
Remaining external dependencies are encoded as explicit hypotheses/goals, not
axioms.

| Category | File(s) | Active axioms | Status |
|---|---|---:|---|
| Switching/shrinkage layer | `pnp3/ThirdPartyFacts/Facts_Switching.lean` | 0 | witness-backed theorems |
| Localized strict bridge | `pnp3/ThirdPartyFacts/PpolyFormula.lean` | 0 | explicit goal hypotheses |
| Partial locality-lift bridge | `pnp3/ThirdPartyFacts/PartialLocalityLift.lean` | 0 | explicit hypotheses (`hStable` / `hCardHalf`) |

---

## External Inputs Still Required (Non-Axiomatic)

1. `GapPartialMCSPPpolyRealToPpolyFormulaGoal p`
   - File: `pnp3/ThirdPartyFacts/PpolyFormula.lean`
   - Role: localized `PpolyReal -> PpolyFormula` bridge for `gapPartialMCSP_Language p`.

2. Witness-backed shrinkage inputs
   - File: `pnp3/ThirdPartyFacts/Facts_Switching.lean`
   - Role: instantiate shrinkage statements via `FamilyIsAC0` / `FamilyIsLocalCircuit` witnesses.

3. Certificate-cardinality obligations (`hCardHalf`-style)
   - File: `pnp3/ThirdPartyFacts/PartialLocalityLift.lean`
   - Role: provide `restriction.alive.card ≤ Partial.tableLen p.n / 2` when using certificate-driven locality lift.

---

## Scope Note

This document tracks axioms. It does not claim the final separation is
unconditional. Current final partial-track statements are conditional on the
explicit external inputs above.
