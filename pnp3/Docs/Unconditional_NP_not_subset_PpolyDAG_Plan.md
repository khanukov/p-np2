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

Current public final theorem still has compatibility shape:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

So there are two closure layers:

1. internalize DAG separation (`hNPDag` removal),
2. remove residual compatibility `hMag`.

## 3. Hard policy: fixed-slice branch is a closed historical no-go route

The literal fixed-slice support-half branch is no longer an active target.
This is documented in code-level no-go modules:

- `LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean`
- `LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean`

Interpretation for planning:

- keep fixed-slice wrappers only as endpoint compatibility plumbing,
- do not spend theorem budget on reviving single-slice blocker hunt.

## 4. Single active theorem route

Only active route for internal DAG separation:

1. Choose one asymptotic family surface (`GapSliceFamily` route already wired).
2. Prove one **eventual** source theorem (for all large enough `n`) in one of
   these forms:
   - accepted-family route, or
   - promise-YES route.
3. Keep bridges **length-local**; avoid all-length global equalities as closure
   assumptions.
4. Use weak-route class-level theorem surface to derive
   `ComplexityInterfaces.NP_not_subset_PpolyDAG` internally.
5. Feed result into existing final wrappers (no new endpoint names).

## 5. Exact immediate theorem target (next merge objective)

Deliver one theorem with concrete shape:

```text
∀ β, 0 < β → β < β0 → ∃ n0, ∀ n ≥ n0, SourceAt(n, β, ε)
```

where `SourceAt` is either:

1. `SmallDAGImpliesAcceptedFamilyAt ...`, or
2. `SmallDAGImpliesPromiseYesSubcubeAt ...`.

Then instantiate the existing eventual closure theorem and weak-route class-level
closure theorem to obtain a branch-local internal DAG separation theorem.

## 6. Integration order after theorem target

1. Introduce internal theorem producing
   `ComplexityInterfaces.NP_not_subset_PpolyDAG`.
2. Switch public final API to stop requiring external `hNPDag`.
3. Then clean residual `hMag` from public theorem surface.

## 7. Non-goals right now

Do not spend next theorem sprint on:

1. adding new wrappers,
2. renaming existing wrappers,
3. reopening fixed-slice blocker hunt,
4. claiming full unconditionality before both `hNPDag` and `hMag` are removed
   from public dependency chain.

## 8. Definition of done

DAG side honestly closed when all hold:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` proved internally.
2. Public final theorem no longer takes external `hNPDag`.
3. Repository remains clean under `./scripts/check.sh`.
4. `README.md`, `STATUS.md`, `TODO.md`, checklist docs are consistent.

Fully unconditional branch when add:

5. Public theorem no longer exposes compatibility-only `hMag`.
6. Zero-argument final theorem `P_ne_NP` is derivable in active tree.
