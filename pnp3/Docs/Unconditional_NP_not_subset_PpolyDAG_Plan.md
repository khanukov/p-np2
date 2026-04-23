# Plan Status For `NP_not_subset_PpolyDAG`

Last updated: 2026-04-23.

This file is the canonical DAG-side route note for the active branch.
Hard policy reference:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## 1. Current Verified State

Already true in repository:

1. `./scripts/check.sh` passes.
2. No active project-local `axiom` and no active `sorry/admit` in `pnp3/`.
3. Inclusion is internalized.
4. DAG endpoint infrastructure is present:
   - fixed-slice `PpolyDAG -> PpolyFormula` bridge;
   - Route-B packaging: `dagRouteBSourceBlocker`, `DAGRouteBSourceClosure`;
   - asymptotic and `_TM` final wrappers;
   - support-half fallback surfaces.

Conclusion:

> Endpoint wiring is not the central blocker.  The central blocker is the
> formula-side support/locality source theorem.

## 2. Refuted Historical Route

The historical route used support bounds for arbitrary formula witnesses:

```text
FormulaSupportRestrictionBoundsPartial
```

The audit proves this predicate is false.  It is refuted by fixed-slice
truth-table hardwiring.  The associated multi-switching contract is also false:

```text
FormulaSupportBoundsFromMultiSwitchingContract -> False
```

Therefore the legacy theorem

```text
NP_not_subset_PpolyDAG_final_of_multiswitchingData
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (D : AsymptoticFormulaTrackData)
```

is not an unconditional result.  Its `hMS` input is already inconsistent.
The asymptotic NP pullback is no longer a separate public argument; it is
constructed from `D.asymptoticNP_TM`.

The public theorem name `NP_not_subset_PpolyDAG_final` is now reserved for the
honest research-gap boundary:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
```

## 3. Pipeline Attempt And Probe 7

The first pipeline-aware replacement,
`FormulaSupportBoundsPartial_fromPipeline`, is also formally ex-falso.

Reason: the internal singleton provider can synthesize per-formula AC0
provenance by fitting AC0 parameters to the formula's truth-table DNF.  This
does not provide a real provenance filter.

## 4. Fixed-Params Candidate

The current candidate contract is:

```text
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

This fixes `ac0` externally, so the known singleton-provider attack no longer
ports directly.  However:

1. fixedParams is not a proved source theorem;
2. fixedParams plus uniform provenance for every formula under the same `ac0`
   reconstructs the old false predicate;
3. the pair `fixedParams + uniformProvenance` is formally inconsistent.

The theorem
`NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance`
exists to expose this exact gap.  It should not be read as mathematical
progress toward an unconditional separation.

The gap is isolated in
`pnp3/Magnification/UnconditionalResearchGap.lean` as `ResearchGapWitness`.
That file already contains the compiled bridge from the witness to `P != NP`.

## 5. Fixed-Slice No-Go Status

The literal fixed-slice support-half branch is not an active target.  This is
documented in code-level no-go modules:

- `LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`
- `LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean`

Interpretation for planning:

- keep fixed-slice wrappers only as endpoint compatibility plumbing;
- do not spend theorem budget on reviving a single-slice blocker hunt.

## 6. What Would Count As Progress

Real progress requires a non-vacuous formula-side theorem that:

1. does not quantify over arbitrary `PpolyFormula` witnesses;
2. cannot be satisfied by truth-table hardwiring;
3. cannot be satisfied by singleton per-formula AC0 provenance;
4. uses fixed, externally meaningful AC0 parameters;
5. does not imply the old false support-bounds predicate.

Only after such a theorem exists should it be wired into the DAG final route.

## 7. Non-Goals

Do not spend the next theorem sprint on:

1. adding final wrappers that hide the support-bounds source;
2. claiming full unconditionality;
3. presenting `fixedParams + uniformProvenance` as a solvable pair;
4. reopening historical fixed-slice blocker hunts.

## 8. Definition Of Done

DAG-side separation is honestly closed only when:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` is proved without false
   support-bounds assumptions;
2. the proof is localized as `ResearchGapWitness` in
   `Magnification.UnconditionalResearchGap`;
3. the formula-side source theorem has its own falsifiability audit;
4. repository remains clean under `./scripts/check.sh`;
5. `README.md`, `STATUS.md`, `TODO.md`, and checklist docs are consistent.
