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

These hypotheses are exposed only by quarantined audit / compatibility
wrappers in `pnp3/Magnification/FinalResultAuditRoutes.lean` and
`pnp3/Magnification/FinalResultLegacyTM.lean`, never by the public default
endpoints.  Per Research Constitution Rule 6, every such endpoint is
prefixed `RefutedRoute_*`, `Vacuous_*`, or `AuditOnly_*` so that a reader
scanning the API can identify it as not-a-claim:

1. `MagnificationAssumptions` — on `RefutedRoute_*` wrappers around the
   `_of_magnification` / `_with_magnification` / `_of_asymptotic_*Route` /
   `_of_asymptotic_blocker` / `_of_asymptotic_sourceClosure` / similar
   compatibility surfaces.
2. `FormulaSupportBoundsFromMultiSwitchingContract` (`hMS`) — on
   `RefutedRoute_*` wrappers around `_of_asymptoticPullback`,
   `_of_multiswitchingData`, and related compatibility shapes.
3. `AsymptoticFormulaTrackHypothesis`, `AsymptoticNPPullback`, provider
   instances — on additional `Vacuous_*` audit wrappers (e.g.
   `Vacuous_P_ne_NP_via_FinalPayloadProvider` and siblings).
4. `_TM` compatibility wrappers (`AuditOnly_*` in
   `FinalResultLegacyTM.lean`) expose `TMWitness` plus the stable
   restriction / certificate / invariant / source-closure / blocker
   shapes; they are not consuming refuted predicates directly but are
   kept off the publishable surface.

All of `MagnificationAssumptions`,
`FormulaSupportRestrictionBoundsPartial`,
`FormulaSupportBoundsFromMultiSwitchingContract`,
`FormulaSupportBoundsPartial_fromPipeline`,
`MagnificationAssumptions_fromPipeline`, and
`FormulaCertificateProviderPartial` are formally refuted by the
falsifiability audit (`-> False`).  Any `RefutedRoute_*` endpoint that
takes one of them is therefore vacuous; it exists only for import
stability and audit attribution.

## Hygiene verification

Primary project check:

```bash
./scripts/check.sh
```
