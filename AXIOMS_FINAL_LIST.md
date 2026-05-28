# Complete Axiom Inventory - PNP3

Updated: 2026-05-28

- Active global `axiom` declarations in `pnp3/`: **0**
- Active `sorry/admit` in `pnp3/`: **0**

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## Scope

This file tracks only axiom/sorry hygiene.  It does not by itself imply
unconditional `P ≠ NP`.

## External assumptions on the current public default

The current public default endpoints are:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
P_ne_NP_final               (gap : ResearchGapWitness)
```

defined in `pnp3/Magnification/UnconditionalResearchGap.lean`.

The only explicit hypothesis on the public default is `ResearchGapWitness`.
Its single mathematical field is:

```text
ResearchGapWitness.dagSeparation : ComplexityInterfaces.NP_not_subset_PpolyDAG
```

There is no `MagnificationAssumptions`, `FormulaSupportBoundsFromMultiSwitchingContract`,
`FormulaSupportBoundsPartial_fromPipeline`, or provider payload on the
public default final theorem.

## External assumptions on audit / legacy wrappers

These hypotheses are exposed only by explicit audit / compatibility wrappers
under `_of_*` names (mostly in
`pnp3/Magnification/FinalResultAuditRoutes.lean`), not by the public default
endpoints:

1. `MagnificationAssumptions` — on
   `P_ne_NP_final_of_magnification` / `NP_not_subset_PpolyDAG_final_of_magnification`.
2. `FormulaSupportBoundsFromMultiSwitchingContract` (`hMS`) — on
   `P_ne_NP_final_of_asymptoticPullback`,
   `P_ne_NP_final_of_multiswitchingData`, and related wrappers.
3. `AsymptoticFormulaTrackHypothesis`, `AsymptoticNPPullback`, provider
   instances — on additional audit / asymptotic wrappers.
4. Various fixed-slice `_TM`, source-closure, blocker, and bridge wrappers
   continue to expose the assumptions appropriate to their theorem surfaces.

All of `MagnificationAssumptions`,
`FormulaSupportRestrictionBoundsPartial`,
`FormulaSupportBoundsFromMultiSwitchingContract`,
`FormulaSupportBoundsPartial_fromPipeline`,
`MagnificationAssumptions_fromPipeline`, and
`FormulaCertificateProviderPartial` are formally refuted by the
falsifiability audit: their existence proves `False`.  The audit / legacy
wrappers above are therefore vacuous as paths to unconditional closure; they
exist only for import stability and historical attribution.

## Hygiene verification

Primary project check:

```bash
./scripts/check.sh
```
