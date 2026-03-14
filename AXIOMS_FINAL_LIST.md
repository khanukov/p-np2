# Complete Axiom Inventory - PNP3

Updated: 2026-03-13

- Active global `axiom` declarations in `pnp3/`: **0**
- Active `sorry/admit` in `pnp3/`: **0**

Canonical unconditional-checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## Scope

This file tracks only axiom/sorry hygiene.
It does not by itself imply unconditional `P ≠ NP`.

## External assumptions still present in active final DAG route

These are explicit hypotheses, not axioms:

1. `NP_not_subset_PpolyDAG`
2. (`default-supportBounds` compatibility wrapper only)
   `hasDefaultFormulaSupportRestrictionBoundsPartial`

Compatibility DAG wrappers (non-default API) still expose explicit inclusion
contract bundles such as `PsubsetPpolyInternalContractsIteratedCanonical`.
