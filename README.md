# P vs NP: Lean Formalization (Honest Status)

Status date: 2026-03-26.

Canonical checklist for unconditional readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.

## What This Project Is

This repository contains a machine-checked (Lean 4) formalization of a route of
the form:

`SAL -> Covering/Lower Bounds -> anti-checker -> magnification -> final wrappers`.

The active `pnp3/` branch is maintained as an auditable contract: what is
constructively formalized now, and what assumptions are still explicit.

## Current State (No Overstatement)

- `pnp3/` builds; `./scripts/check.sh` passes.
- Active `axiom` declarations in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- Audited theorem surface still uses standard Lean assumptions
  `propext`, `Classical.choice`, `Quot.sound` (but no project-local axioms).
- Final entrypoints are in `pnp3/Magnification/FinalResult.lean`.
- Final `P ≠ NP` wrappers are conditional (including the new
  support-bounds + `DAG → Formula` TM wrappers on the DAG side).
- DAG barrier layer is now split into an explicit theorem-level asymptotic
  module `pnp3/LowerBounds/AsymptoticDAGBarrier.lean` with
  `GapSliceFamily`, per-slice anti-locality/locality contracts, and the
  magnification-style endpoint
  `MagnificationStyleNoSmallDAG`.
- Layer B is now small-solver aware: locality contracts quantify over circuits
  satisfying an explicit size predicate
  `SizeBound n β ε (DagCircuit.size C)`, not over arbitrary correct circuits.
- DAG Route-B source code now has both legacy language-level slack bridge and
  witness-indexed bridge in
  `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
  (`SmallDAGWitnessOnSlice`, `DAGStableRestrictionSlackPackageAt`,
  `smallDAGLocalityStatement_of_dagSlackPackageAtProvider`).
- The route remains conditional on proving the slice-level small-DAG locality
  mathematics (no unconditional `P ≠ NP` theorem yet).

Bottom line today: there is no unconditional in-repo theorem `P ≠ NP`.

## Active Final DAG Boundary

Current default final endpoint `P_ne_NP_final` depends on:

1. `NP_not_subset_PpolyDAG`

So the open work is now explicitly DAG-side, not just formula-side wording.

## Inclusion-Side Progress (`P ⊆ PpolyDAG`)

Already closed in code:

1. internal linear one-step provider
   `stepCompiledLinearCandidateStepSpecProvider_internal`
2. internal linear size closure
   `compiledRuntimeCircuitSizeBoundLinear_internal`
3. internal linear correctness
   `compiledRuntimeAcceptCorrectnessLinear_internal`
4. internal no-arg linear output-wire agreement
   `compiledAcceptOutputWireAgreementLinear_internal`
5. no-arg inclusion theorem
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`

Still open for unconditional final route:

1. internalize `NP_not_subset_PpolyDAG`

## How To Verify State

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean; do
  lake env lean "$f"
done
```

## Primary Documents

- `STATUS.md` - authoritative current snapshot.
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` - canonical blocker checklist.
- `RELEASE_RC.md` - release messaging/checklist for current RC state.
- `TODO.md` - execution order for remaining closure tasks.
- `PROOF_OVERVIEW.md` - proof-route map for auditors.
- `FAQ.md` - short reviewer-facing clarifications.
- `AXIOMS_FINAL_LIST.md` - axiom/sorry hygiene inventory only.

## Wording Policy

Until the checklist is fully closed, any `P ≠ NP` statement in this repository
must explicitly indicate that final theorems are conditional.
