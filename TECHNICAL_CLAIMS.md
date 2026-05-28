# Technical Claims and Scope

Updated: 2026-05-28

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current milestone release guardrail:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## Verified claim level

1. Active `pnp3/` tree is axiom-clean (`axiom = 0`, `sorry/admit = 0`).
2. `./scripts/check.sh` passes on the current tree.
3. Current audit/regression tests pass on the current tree
   (`AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
   `BridgeLocalityRegression`, `WeakRouteSurfaceTests`,
   `FormulaSupportBoundsFalsifiabilityProbe`).
4. Inclusion is internalized through
   `Simulation.proved_P_subset_PpolyDAG_internal`.
5. The DAG side has compiled fixed-slice/asymptotic wrappers,
   source-closure/blocker wrappers, support-half fallback surfaces, and
   canonical witness-density compiler infrastructure.  The single public
   closure boundary on top of this plumbing is
   `pnp3/Magnification/UnconditionalResearchGap.lean`.
6. Active theorem surfaces still use standard Lean assumptions
   `propext`, `Classical.choice`, `Quot.sound`, but no project-local axioms.
7. The legacy support-bounds / multi-switching surfaces
   (`FormulaSupportRestrictionBoundsPartial`,
   `FormulaSupportBoundsFromMultiSwitchingContract`,
   `MagnificationAssumptions`,
   `FormulaSupportBoundsPartial_fromPipeline`,
   `MagnificationAssumptions_fromPipeline`,
   `FormulaCertificateProviderPartial`)
   are formally refuted: their existence proves `False` in the audit module.
   Any final wrapper that consumes one of them is therefore vacuous.

## What is the current public closure boundary?

The public default endpoints are:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
P_ne_NP_final               (gap : ResearchGapWitness)
```

They are defined in
`pnp3/Magnification/UnconditionalResearchGap.lean`.  The only mathematical
input is `gap.dagSeparation : ComplexityInterfaces.NP_not_subset_PpolyDAG`.

`hMag`, `hMS`, `hAsym`, `hNPbridge`, and provider-backed entry points are
preserved only as quarantined audit / compatibility wrappers in
`pnp3/Magnification/FinalResultAuditRoutes.lean` and
`pnp3/Magnification/FinalResultLegacyTM.lean`.  Per Research Constitution
Rule 6, every such endpoint carries the prefix `RefutedRoute_*`,
`Vacuous_*`, or `AuditOnly_*` so that a reader scanning the API
immediately sees that it is not the public closure boundary.

## Not currently claimed

1. No unconditional in-repo theorem `P ≠ NP`.
2. No non-vacuous proof of `ResearchGapWitness`.
3. No zero-argument `P_ne_NP_unconditional`; the template is kept commented
   out inside `UnconditionalResearchGap.lean` and is enabled only when the
   research witness is supplied.
4. No claim that the legacy `MagnificationAssumptions`,
   `FormulaSupportBoundsFromMultiSwitchingContract`, or
   `FormulaSupportBoundsPartial_fromPipeline` routes can be revived as a
   path to unconditional closure: they are vacuous in the current tree.

## Rule for public wording

Any statement of `P ≠ NP` must mention that the public final theorem is still
conditional on `ResearchGapWitness`, and must not present the legacy
support-bounds / multi-switching audit wrappers as the canonical path, until
the checklist in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` is fully closed.
