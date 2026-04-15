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

Current public default theorem is:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
```

The DAG side is already closed on this path:

1. `NP_not_subset_PpolyDAG_final hMag` is internalized;
2. no external DAG payload remains on the default theorem surface.

### Target 2. Remove remaining public `hMag`

Theorem is still not zero-arg while it takes `hMag` for compatibility.

To reach a genuinely unconditional top-level theorem, still need either:

1. full API cleanup/internalization that removes compatibility `hMag`; or
2. a fully internal route proving the same payload without exposing
   magnification assumptions in the public theorem surface.

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

1. an internal source for
   `NP_not_subset_PpolyFormula_final (hMag : MagnificationAssumptions)`;
2. equivalently, an internal source for the magnification package pieces used
   by the formula and `PpolyReal` finals;
3. a zero-argument wrapper that no longer exposes `hMag`.

Acceptance condition:

- `UNCONDITIONAL=1 ./scripts/check.sh` no longer reports
  `NP_not_subset_PpolyFormula_final` as depending on
  `MagnificationAssumptions`.

### Task 3. Keep internal DAG separation closed

Status: completed, preserve.

Delivery condition:

- keep `NP_not_subset_PpolyDAG_final (hMag)` deriving class-level DAG
  separation with no external DAG payload.

### Task 4. Replace compatibility final theorem surface

Status: pending on Task 2.

Current theorem:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
```

Required end state:

- no residual `hMag` in public endpoint.

### Task 5. Final consistency pass

Status: pending.

After theorem closure:

1. update `README.md`, `STATUS.md`, `TODO.md`, `CHECKLIST_*`, release docs;
2. rerun full `./scripts/check.sh` and audit tests.

## Non-Goals Right Now

- Do not add wrappers just to show apparent progress.
- Do not reopen fixed-slice support-half as a primary theorem target.
- Do not claim full unconditionality while `hMag` remains in public theorem.
