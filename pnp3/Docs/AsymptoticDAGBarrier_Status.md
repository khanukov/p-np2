# Asymptotic DAG Barrier Status

Updated: 2026-04-15

This note records the **current** role of the asymptotic DAG barrier layer
after DAG-side internalization moved the default blocker elsewhere.

## 1. What the barrier layer already provides

The asymptotic/barrier stack already contains:

1. slice-family packaging via `GapSliceFamily`;
2. per-slice small-DAG witness extraction surfaces;
3. bridges from per-slice/global `PpolyDAG` witnesses into `SmallDAGSolver`
   surfaces;
4. contradiction schemas from asymptotic no-small-solver hypotheses to
   `¬ PpolyDAG`;
5. weak-route class-level wrappers such as
   `NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute` and
   `NP_not_subset_PpolyDAG_of_promiseYesWeakRoute`.

So the asymptotic layer is real infrastructure, not a plan stub.

## 2. Current role after DAG internalization

The barrier layer remains important infrastructure, but it is no longer the
current blocker for the default final theorem.

Default DAG separation is already internalized in `NP_not_subset_PpolyDAG_final`
through a different route. So the barrier layer should now be read primarily as
research / alternative-route infrastructure.

## 3. Current structural limitation

Two blocker facts are now explicit in code:

1. `gapSliceFamily_isEmpty : IsEmpty GapSliceFamily`;
2. fixed-slice blocker lemmas are only usable in conditional form (they
   expose incompatibility once fixed-slice `PpolyDAG` membership is available).

So the original all-slices carrier and bridge shape are not just “hard”, but
structurally mis-specified for the intended asymptotic route.

The current global witness bridge is also stronger than the data coming from
the public magnification package.

Specifically:

1. `AsymptoticDAGLanguageBridge` requires one global language agreeing with all
   slice languages for all `N`;
2. `MagnificationAssumptions` currently provides only target-slice agreement
   (`sliceEq`) at the chosen slice length.

Therefore the all-slices barrier program remains mathematically meaningful, but
it is not the current blocker for cleaning up the public final theorem.

## 4.5 Concrete next refactor target (recommended)

The next non-vacuous route should use the new eventual scaffolding:

1. `GapSliceFamilyEventually` (index obligations only for `n ≥ N0`);
2. `AsymptoticDAGSliceBridgeAt` (agreement only on the encoded length of each
   target slice, not on all lengths).

Concretely, the next implementation step is:

- migrate theorem surfaces that currently quantify over `GapSliceFamily` to the
  eventual family variant;
- replace all-length bridge assumptions with length-local bridge assumptions;
- keep fixed-slice wrappers as compatibility endpoints while rebuilding the
  all-slices program on the eventual interfaces.

## 5. Current best use of the barrier layer

### Immediate use

Use the asymptotic layer as a theorem laboratory for alternative DAG routes and
for stronger standalone non-uniform separation statements.

It is no longer necessary to route the default final theorem through this layer
before attacking the remaining unconditional blocker.

### Longer-term use

Keep the all-slices weak-route / canonical-family route as the stronger
standalone theorem program for an internal `NP_not_subset_PpolyDAG` that does
not depend on the current fixed-slice integration path.

## 6. What the barrier layer does not yet solve by itself

The barrier layer still does **not** by itself provide:

1. a zero-argument theorem `P_ne_NP`;
2. a replacement for the current public compatibility argument `hMag`;
3. a formula-side internalization of the remaining public package surface.

Those require source mathematics outside the barrier layer.

## 7. Recommended reading order

If you want the shortest accurate picture:

1. `pnp3/LowerBounds/AsymptoticDAGBarrier.lean`
2. `pnp3/LowerBounds/DAGUnconditionalBlocker.lean`
3. `pnp3/Magnification/FinalResultCore.lean`
4. `pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`
