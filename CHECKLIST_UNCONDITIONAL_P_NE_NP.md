# Checklist: Unconditional Constructive `P != NP`

Updated: 2026-04-23

This is the canonical checklist for what still blocks an unconditional
in-repo theorem `P != NP`.

For current release posture, see `RELEASE_RC.md`.
For hard route policy lock, see `pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## Current Final API (actual code)

Files:

- compatibility import path: `pnp3/Magnification/FinalResult.lean`
- active research-gap surface:
  `pnp3/Magnification/UnconditionalResearchGap.lean`
- legacy/audit route surface:
  `pnp3/Magnification/FinalResultAuditRoutes.lean`

Current public endpoints:

```text
NP_not_subset_PpolyDAG_final
  (gap : ResearchGapWitness)

P_ne_NP_final
  (gap : ResearchGapWitness)
```

Provider/support-bounds endpoints are retained only as explicit audit routes,
for example:

```text
P_ne_NP
  [FinalPayloadProvider]

P_ne_NP_final_of_asymptoticPullback
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
```

Those audit routes are not unconditional theorems.  The `hMS` component is
part of the formally refuted support-bounds route.

## Already Closed

1. Active `pnp3/` tree is axiom-clean (`axiom = 0`, `sorry/admit = 0`).
2. `./scripts/check.sh` passes on current tree.
3. Inclusion is internalized via
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
4. DAG endpoint wiring and fixed-slice `PpolyDAG -> PpolyFormula` conversion
   are implemented.
5. Historical fixed-slice support-half branch is archived as a no-go route:
   - `FailedRoute_FixedSliceSupportHalfCore.lean`
   - `FailedRoute_FixedSliceSupportHalfImpossible.lean`.

## Refuted Assumption Surfaces

The support-bounds audit proves that these surfaces are vacuous:

1. `FormulaSupportRestrictionBoundsPartial -> False`
2. `FormulaSupportBoundsFromMultiSwitchingContract -> False`
3. `MagnificationAssumptions -> False`
4. `FormulaSupportBoundsPartial_fromPipeline -> False`
5. `MagnificationAssumptions_fromPipeline -> False`

Therefore, proving final statements from these assumptions is not mathematical
progress toward unconditional `P != NP`.

## Fixed-Params Candidate

The active nontrivial candidate shape is:

```text
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

Current audit status:

1. fixed external `ac0` blocks the known Probe 7 singleton-provider attack;
2. fixedParams alone is not currently refuted in-project;
3. fixedParams plus uniform provenance for every formula witness under the
   same `ac0` implies the old false predicate;
4. the pair `fixedParams + uniformProvenance` is formally inconsistent.

## Remaining Unconditional Blocker

Full unconditionality requires a non-vacuous proof of `ResearchGapWitness`,
equivalently `ComplexityInterfaces.NP_not_subset_PpolyDAG`.  Any lower-level
support/locality theorem used to obtain it must:

1. avoid universal quantification over arbitrary `PpolyFormula` witnesses;
2. reject truth-table hardwiring and singleton provenance;
3. use fixed, externally meaningful AC0 parameters;
4. not imply `FormulaSupportRestrictionBoundsPartial`;
5. connect to the existing DAG endpoint plumbing without routing through the
   old `FormulaSupportBoundsFromMultiSwitchingContract`.

This is a research-level lower-bound gap, not a missing wrapper.

The gap is isolated in
`pnp3/Magnification/UnconditionalResearchGap.lean`.  The file defines
`ResearchGapWitness` and already proves
`P_ne_NP_of_researchGap : ResearchGapWitness -> P_ne_NP`.

## Proof-Quality Safety Checks

Before declaring any blocker closed, confirm:

1. `./scripts/check.sh` passes.
2. Current audit/regression tests pass:
   `pnp3/Tests/AxiomsAudit.lean`,
   `pnp3/Tests/BarrierAudit.lean`,
   `pnp3/Tests/BarrierBypassAudit.lean`,
   `pnp3/Tests/BridgeLocalityRegression.lean`,
   `pnp3/Tests/WeakRouteSurfaceTests.lean`,
   `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.
3. New source assumptions have a falsifiability audit before they are used by
   final theorem surfaces.
4. No document claims unconditional `P != NP` prematurely.

## Definition Of Done

All of the following must hold at once:

1. A non-vacuous formula-side source theorem replaces the refuted
   support-bounds/multi-switching route.
2. `ResearchGapWitness` is proved in
   `pnp3/Magnification/UnconditionalResearchGap.lean`.
3. `ComplexityInterfaces.NP_not_subset_PpolyDAG` is derived without false or
   externally supplied research assumptions.
4. Public final theorem no longer depends on external provider payload.
5. Zero-argument theorem `P_ne_NP` is derivable in the active tree.
6. Canonical docs are updated consistently to unconditional wording.
