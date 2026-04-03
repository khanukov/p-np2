# Complete Axiom Inventory - PNP3

Updated: 2026-04-03

- Active global `axiom` declarations in `pnp3/`: **0**
- Active `sorry/admit` in `pnp3/`: **0**

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## Scope

This file tracks only axiom/sorry hygiene.
It does not by itself imply unconditional `P ≠ NP`.

## External assumptions still present in active final routes

These are explicit hypotheses, not axioms:

1. `NP_not_subset_PpolyDAG` on the current public default final theorem.
2. `MagnificationAssumptions` on the current public default final theorem.
3. Various fixed-slice `_TM`, source-closure, blocker, and bridge wrappers
   continue to expose the assumptions appropriate to their theorem surfaces.

## Hygiene verification

Primary project check:

```bash
./scripts/check.sh
```
