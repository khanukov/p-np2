# Gap-Target Stable-Restriction Route Status

Last updated: 2026-04-15.

This note records the **current** state of the fixed-slice stable-restriction /
Route-B route after the recent blocker-packaging and fallback-closure work.

Current status caveat: this is now a **historical route note**, not the main
blocker note for unconditionality. The default DAG separation is already
internalized elsewhere via the fixed-slice `DAG -> Formula` bridge plus the
support-bounds consumer.

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

## 2. What is still missing on this route

What is still not done is one **actual fixed-slice source theorem**.

The shortest honest target is now:

```text
gapPartialMCSP_supportHalfObligation p
```

or equivalently one of:

- `dagRouteBSourceBlocker p`
- `dag_stableRestriction_producer p`

for the chosen fixed slice.

That theorem is the real remaining blocker on this route family.

## 3. Why this route still matters

This route remains mathematically relevant because it still gives one explicit
family of source-side witnesses for DAG contradiction theorems.

But it is no longer the current practical shortest path to the public final API.

The current blocker for unconditionality is the residual
`hMag : MagnificationAssumptions` on the formula/public final cone.

## 4. What this route still does not give automatically

Even after the fixed-slice blocker is proved and fed through the asymptotic
wrapper layer, that still does **not** automatically yield a zero-argument
unconditional theorem, because the current public theorem still exposes
`hMag : MagnificationAssumptions`.

So this route is now a useful subroute, but not the active blocker for
removing `hMag`.

## 5. Current recommendation

Treat this file as a status note for one historical DAG-source route family.
Do not treat it as the canonical current blocker note for unconditionality.
