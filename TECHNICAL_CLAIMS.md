# Technical Claims and Scope

Updated: 2026-03-14

Canonical unconditional-checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current milestone release guardrail:
`RELEASE_RC.md`.

## Verified claim level

1. Active `pnp3/` tree is axiom-clean (`axiom = 0`, `sorry/admit = 0`).
2. `./scripts/check.sh` passes on current tree.
3. Current audit/regression tests pass on current tree
   (`AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
   `BridgeLocalityRegression`).
4. Active final wrappers for `P ≠ NP` remain conditional on explicit DAG-side
   hypotheses.
5. Internal no-arg inclusion theorem exists:
   `Simulation.proved_P_subset_PpolyDAG_internal`.

## Not currently claimed

1. No unconditional in-repo theorem `P ≠ NP`.
2. No unconditional default final wrapper `P_ne_NP_final` (still expects
   external DAG-separation assumption `NP_not_subset_PpolyDAG`).

## Rule for public wording

Any statement of `P ≠ NP` must mention conditional assumptions until the
checklist in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` is fully closed.
