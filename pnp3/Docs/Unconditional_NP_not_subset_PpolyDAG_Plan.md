# Concrete plan to reach unconditional `NP ⊄ PpolyDAG`

Last updated: 2026-04-04.

This file is the canonical DAG-side theorem plan for the active branch.
Hard policy reference:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## 1. Current verified state

Already true in repository:

1. `./scripts/check.sh` passes.
2. No active project-local `axiom` and no active `sorry/admit` in `pnp3/`.
3. Endpoint plumbing is in place:
   - Route-B packaging: `dagRouteBSourceBlocker`, `DAGRouteBSourceClosure`.
   - Final wrappers: asymptotic and `_TM` surfaces in magnification finals.
4. Weak-route class-level surfaces are implemented:
   - `NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute`,
   - `NP_not_subset_PpolyDAG_of_promiseYesWeakRoute`.
5. Eventual magnification-style aggregation lemmas are implemented:
   - `magnificationStyleNoSmallDAG_of_eventually_acceptedFamily`,
   - `magnificationStyleNoSmallDAG_of_eventually_promiseYesSubcube`.

Conclusion:

> endpoint wiring is not the blocker; source theorem debt is the blocker.

## 2. What is still not closed

Still missing internal theorem:

```text
ComplexityInterfaces.NP_not_subset_PpolyDAG
```

without external DAG-separation input.

Current public final theorem has compatibility shape:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
```

So there is now one remaining closure layer:

1. remove residual compatibility `hMag`.

## 3. Hard policy: fixed-slice branch is a closed historical no-go route

The literal fixed-slice support-half branch is no longer an active target.
This is documented in code-level no-go modules:

- `LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`
- `LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean`

Interpretation for planning:

- keep fixed-slice wrappers only as endpoint compatibility plumbing,
- do not spend theorem budget on reviving single-slice blocker hunt.

## 4. Status of the DAG plan

This plan is now completed in the active tree.

Current mainline route:

1. choose the threshold slice `n = N0`,
2. convert any fixed-slice DAG witness on that slice to a formula witness via
   `Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`,
3. combine with formula-support bounds from `hMag.switching.multiswitching`,
4. feed the result through the already-closed fixed-slice collapse consumer,
5. obtain internal `NP_not_subset_PpolyDAG_final hMag`,
6. then derive `P_ne_NP_final hMag`.

## 5. What remains after DAG closure

The remaining unconditional blocker is no longer DAG separation.
It is the residual formula-side compatibility package exposed by:

```text
NP_not_subset_PpolyFormula_final
  (hMag : MagnificationAssumptions)
```

## 6. Integration order after theorem target

1. DAG-side merge step is done: public final API no longer requires external
   class-level DAG separation.
2. Next clean residual `hMag` from the public theorem surface.

## 7. Non-goals right now

Do not spend next theorem sprint on:

1. adding new wrappers,
2. renaming existing wrappers,
3. reopening historical DAG-side blocker hunts,
4. claiming full unconditionality before `hMag` is removed from the
   public dependency chain.

## 8. Definition of done

DAG side honestly closed when all hold:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` proved internally.
2. Public final theorem no longer takes external class-level DAG separation.
3. Repository remains clean under `./scripts/check.sh`.
4. `README.md`, `STATUS.md`, `TODO.md`, checklist docs are consistent.

Fully unconditional branch when add:

5. Public theorem no longer exposes compatibility-only `hMag`.
6. Zero-argument final theorem `P_ne_NP` is derivable in active tree.
