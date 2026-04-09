# Gap-Target Stable-Restriction Route Status

Last updated: 2026-04-03.

This note records the **current** state of the fixed-slice stable-restriction /
Route-B route after the recent blocker-packaging and fallback-closure work.

## 1. What is already finished

### Consumer side

The fixed-slice consumer stack is already real and compiled:

```text
stable restriction
  -> locality / accepted-family contradiction
  -> no small DAG
  -> class-level DAG non-inclusion surface
```

This is no longer merely architectural.

### Producer-side packaging

The Route-B gate is now normalized explicitly:

- `dagRouteBSourceBlocker`
- `DAGRouteBSourceClosure`
- direct final wrappers from source closure / blocker

### Restricted-model fallback

Support-half fallback now already closes downstream:

- `noSmallDAG_of_supportHalfBoundFamily`
- `NP_not_subset_PpolyDAG_surface_of_supportHalfBoundFamily`

So support-half is no longer just a diagnostic restricted-model note.

## 2. What is still missing

What is still not done is one **actual fixed-slice source theorem**.

The shortest honest target is now:

```text
gapPartialMCSP_supportHalfObligation p
```

or equivalently one of:

- `dagRouteBSourceBlocker p`
- `dag_stableRestriction_producer p`

for the chosen fixed slice.

That theorem is the real remaining blocker on this route.

## 3. Why this route matters now

This route has become more important, not less, because
`Magnification/FinalResultCore.lean` now already contains asymptotic wrappers
that turn one fixed-slice blocker into a class-level DAG-separation statement
(`FinalResult.lean` remains the compatibility import path).

So the current practical shortest path is:

1. prove one fixed-slice blocker;
2. collapse it through the asymptotic wrapper layer;
3. remove external `hNPDag` from the current public final route.

## 4. What this route still does not give automatically

Even after the fixed-slice blocker is proved and fed through the asymptotic
wrapper layer, that still does **not** automatically yield a zero-argument
unconditional theorem, because the current public theorem still exposes
`hMag : MagnificationAssumptions`.

So this route is currently the best path to remove `hNPDag`, but not by itself
the full story for removing `hMag`.

## 5. Current recommendation

Treat this file as the status note for the **fastest current integration
route**.

Treat the stronger all-slices canonical witness-density / witness-transfer
route as a parallel theorem program, not as the shortest immediate blocker for
the public final API.
