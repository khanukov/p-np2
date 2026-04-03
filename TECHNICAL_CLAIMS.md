# Technical Claims and Scope

Updated: 2026-04-03

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current milestone release guardrail:
`RELEASE_RC.md`.

## Verified claim level

1. Active `pnp3/` tree is axiom-clean (`axiom = 0`, `sorry/admit = 0`).
2. `./scripts/check.sh` passes on the current tree.
3. Current audit/regression tests pass on the current tree
   (`AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
   `BridgeLocalityRegression`, `WeakRouteSurfaceTests`).
4. Inclusion is internalized through
   `Simulation.proved_P_subset_PpolyDAG_internal`.
5. The DAG side now has compiled fixed-slice/asymptotic wrappers,
   source-closure/blocker wrappers, support-half fallback surfaces, and
   canonical witness-density compiler infrastructure.
6. Active theorem surfaces still use standard Lean assumptions
   `propext`, `Classical.choice`, `Quot.sound`, but no project-local axioms.

## Not currently claimed

1. No unconditional in-repo theorem `P ≠ NP`.
2. No internal theorem `ComplexityInterfaces.NP_not_subset_PpolyDAG`.
3. No unconditional default public wrapper `P_ne_NP_final`; it still takes
   `hNPDag`, and it still exposes `hMag` as compatibility context.

## Rule for public wording

Any statement of `P ≠ NP` must mention conditional assumptions until the
checklist in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` is fully closed.
