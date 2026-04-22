# TODO / Roadmap (current)

Updated: 2026-04-04

Canonical checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release wording guardrail:
`RELEASE_RC.md`.
Current DAG plan:
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## Snapshot

- Active `axiom` in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes.
- Inclusion is already internalized.
- Remaining debt is theorem-level source mathematics.

## Hard policy update: fixed-slice branch is not an active target

The fixed-slice support-half blocker branch is now treated as a closed
historical no-go direction for unconditional closure planning.

This is already reflected by dedicated failed-route modules:

- `LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`
- `LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean`

So roadmap execution must not prioritize proving unconditional separation from a
literal single fixed slice.

## The Remaining Closure Targets

### Target 1. Keep internal DAG separation closed

Current explicit final theorem is:

```text
P_ne_NP_final
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
```

Current public zero-arg endpoint is:

```text
P_ne_NP
  [FinalPayloadProvider]
```

The DAG side is already closed on this path:

1. `NP_not_subset_PpolyDAG_final hMS hAsym hNPbridge` is internalized;
2. no external DAG payload remains on the default theorem surface.

### Target 2. Remove remaining external provider payload

Public theorem is now zero-arg syntactically, but still depends on external
provider payload (`FinalPayloadProvider` carrying `hMS/hAsym/hNPbridge`).

Formula-side progress:

- `hMS` is now reconstructible from default support-bounds source
  (`hasDefaultFormulaSupportRestrictionBoundsPartial`) via
  `P_ne_NP_of_default_formulaSource`.

To reach a genuinely unconditional top-level theorem, still need either:

1. full internalization that removes remaining provider payload; or
2. a fully internal route proving the same payload without exposing
   these assumptions in the public theorem surface.

## Execution Order

### Task 1. Keep docs and audit wording strict

Status: active discipline.

Rule:

- do not claim unconditional `P ≠ NP` yet;
- do not present fixed-slice historical branch as current closure plan;
- keep a single canonical active route across docs.

### Task 2. Internalize the formula-side final surface (main blocker)

Status: active blocker.

Immediate theorem targets:

1. preserve and harden default formula-side internal source for `hMS`;
2. internalize the remaining asymptotic payload (`hAsym/hNPbridge`) still
   exposed via provider classes;
3. a zero-argument wrapper with no external provider payload.

Acceptance condition:

- `UNCONDITIONAL=1 ./scripts/check.sh` no longer reports default finals as
  depending on external provider payload.

### Task 3. Keep internal DAG separation closed

Status: completed, preserve.

Delivery condition:

- keep `NP_not_subset_PpolyDAG_final (hMag)` deriving class-level DAG
  separation with no external DAG payload.

### Task 4. Remove residual provider payload from public endpoint

Status: pending on Task 2.

Current explicit theorem:

```text
P_ne_NP_final
  (hMS : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract)
  (hAsym : AsymptoticFormulaTrackHypothesis)
  (hNPbridge : AsymptoticNPPullback hAsym)
```

Required end state:

- public zero-arg endpoint has no residual external provider payload.

### Task 5. Final consistency pass

Status: pending.

After theorem closure:

1. update `README.md`, `STATUS.md`, `TODO.md`, `CHECKLIST_*`, release docs;
2. rerun full `./scripts/check.sh` and audit tests.

## Non-Goals Right Now

- Do not add wrappers just to show apparent progress.
- Do not reopen fixed-slice support-half as a primary theorem target.
- Do not claim full unconditionality while public endpoint still depends on
  external provider payload (`FinalPayloadProvider` /
  `AsymptoticPayloadProvider`).
