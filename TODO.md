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

## The Two Remaining Closure Targets

### Target 1. Internalize `NP_not_subset_PpolyDAG` via asymptotic/eventual route

Current public default theorem still requires:

```text
hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG
```

Active theorem route is exactly:

1. prove one eventual source theorem on a non-vacuous surface;
2. use length-local bridge assumptions (not all-length global bridge claims);
3. close one weak-route class-level payload (`acceptedFamily` or
   `promiseYes` family);
4. reconnect to existing wrappers without adding new endpoint plumbing.

### Target 2. Remove remaining public `hMag`

Even after Target 1 is done, theorem is not yet zero-arg while it still takes
`hMag` for compatibility.

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

### Task 2. Prove one eventual weak-route source theorem (main blocker)

Status: active blocker.

Immediate theorem targets:

1. one eventual accepted-family or promise-YES theorem with explicit
   `n ≥ n0(β)` shape;
2. one length-local bridge theorem sufficient to push global `PpolyDAG` witness
   down to the targeted slices;
3. one class-level contradiction payload consumable by existing wrappers.

Acceptance condition:

- at least one existing asymptotic wrapper is callable from the new eventual
  source theorem, without new endpoint names.

### Task 3. Internalize `NP_not_subset_PpolyDAG`

Status: pending on Task 2.

Delivery condition:

- produce internal theorem
  `ComplexityInterfaces.NP_not_subset_PpolyDAG`
  with no external DAG-separation assumption.

### Task 4. Replace compatibility final theorem surface

Status: pending on Task 3.

Current theorem:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

Required end state:

- no external `hNPDag` and then no residual `hMag` in public endpoint.

### Task 5. Final consistency pass

Status: pending.

After theorem closure:

1. update `README.md`, `STATUS.md`, `TODO.md`, `CHECKLIST_*`, release docs;
2. rerun full `./scripts/check.sh` and audit tests.

## Non-Goals Right Now

- Do not add wrappers just to show apparent progress.
- Do not reopen fixed-slice support-half as a primary theorem target.
- Do not claim that removing only `hNPDag` yields full unconditionality while
  `hMag` remains in public theorem.
