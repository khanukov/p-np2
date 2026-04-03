# Concrete plan to reach unconditional `NP ⊄ PpolyDAG`

Last updated: 2026-04-03.

This file tracks the **current** DAG-side closure plan after the latest
hardwire-coverage, support-half fallback, and asymptotic fixed-slice wrapper
work.

It is intentionally narrower than older roadmap notes. The main goal here is
to state what is already done, what is still open, and what the shortest honest
next theorem is.

## 1. Current verified state

The repository now already has:

1. `./scripts/check.sh` passing on the active tree.
2. No active project-local `axiom` and no active `sorry/admit` in `pnp3/`.
3. Route-B blocker packaging:
   `dagRouteBSourceBlocker`,
   `DAGRouteBSourceClosure`,
   direct `_TM` finals from stable restriction / source closure / blocker.
4. Asymptotic fixed-slice wrappers:
   `NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse`,
   `..._of_asymptotic_dag_stableRestriction`,
   `..._of_asymptotic_sourceClosure`,
   `..._of_asymptotic_blocker`,
   plus companion `P_ne_NP_final_of_*`.
5. Canonical witness-density hardwire coverage:
   `canonicalEasyFamilyRealizesAllPatternsUpTo_of_hardwireCircuitBound`.
6. Canonical all-slices compiler glue:
   `canonical_smallDAG_witnessEasyDensity_source_on_slices_of_supportBudget`,
   `...witnessUniformLower...`,
   `...witnessTransferQuarter...`,
   and their support-half-family variants.
7. Support-half fallback closure to class-level DAG non-inclusion:
   `noSmallDAG_of_supportHalfBoundFamily` and
   `NP_not_subset_PpolyDAG_surface_of_supportHalfBoundFamily`.

Conclusion:

> The repository is no longer blocked on DAG endpoint plumbing.
> The remaining debt is theorem-level.

## 2. What is still not closed

There is still no internal theorem

```text
ComplexityInterfaces.NP_not_subset_PpolyDAG
```

and therefore the public default final theorem is still:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

Important split:

1. `hNPDag` is the real DAG-separation blocker.
2. `hMag` remains in the public theorem only as compatibility context and is
   not consumed by its current implementation.

So there are really two closure goals:

1. remove external `hNPDag`;
2. then remove the residual public `hMag`.

## 3. Fastest current route to remove `hNPDag`

The shortest honest route is now **fixed slice + asymptotic collapse**.

### Step A. Pick one slice from the existing magnification package

Use

```text
p* := hMag.antiChecker.asymptotic.pAt n hn
```

### Step B. Prove one fixed-slice DAG source theorem on `p*`

Preferred targets, in order:

1. `gapPartialMCSP_supportHalfObligation p*`
2. `dagRouteBSourceBlocker p*`
3. `dag_stableRestriction_producer p*`

These are effectively equivalent fixed-slice entry points for the current DAG
consumer stack.

### Step C. Consume it through the already compiled wrappers

Once Step B is proved, the existing theorems already close the route:

1. `NP_not_subset_PpolyDAG_final_of_asymptotic_blocker`
2. `P_ne_NP_final_of_asymptotic_blocker`

or the corresponding stable-restriction / source-closure variants.

This is the shortest current path because:

1. it uses one fixed-slice theorem rather than a full all-slices theorem;
2. the asymptotic collapse layer already exists in code;
3. it matches the current public API shape directly.

## 4. Fastest route to full zero-argument unconditionality

Removing `hNPDag` from the current compatibility theorem is not yet the same as
producing a zero-argument theorem.

The shortest credible route to a true unconditional final theorem is:

1. choose a concrete fixed slice `p*`;
2. provide a concrete `GapPartialMCSP_TMWitness p*`;
3. prove a fixed-slice blocker on `p*`;
4. use the existing `_TM` finals:
   `NP_not_subset_PpolyDAG_final_of_blocker_TM`,
   `P_ne_NP_final_of_blocker_TM`.

This route bypasses `hMag` completely.

Alternative:

- internalize `MagnificationAssumptions` instead of bypassing them.

## 5. Where the canonical all-slices route now stands

The repository also already contains the infrastructure for the stronger
canonical all-slices program:

- `canonical_smallDAG_witnessEasyDensity_source_on_slices`
- `canonical_smallDAG_witnessUniformLower_source_on_slices`
- `canonical_smallDAG_witnessTransferQuarter_source_on_slices`
- compilers from extraction/support budgets into those debts

This remains a legitimate theorem program for a standalone internal
`NP_not_subset_PpolyDAG`.

However, it is **not** the shortest current route to cleaning up the existing
public final API, because:

1. fixed-slice asymptotic wrappers are already present;
2. the current `AsymptoticDAGLanguageBridge` is stronger than the
   `sliceEq` data provided by `MagnificationAssumptions`;
3. one fixed-slice blocker is sufficient for the currently exposed asymptotic
   final wrappers.

## 6. Recommended execution order

### Immediate theorem target

Prove one fixed-slice DAG source theorem, preferably
`gapPartialMCSP_supportHalfObligation p*`.

### Immediate integration target

Use that theorem to construct an internal
`NP_not_subset_PpolyDAG` route for the current `hMag`-based final interface.

### Then

Replace the current compatibility theorem with a theorem that no longer takes
external `hNPDag`.

### Then

Finish the remaining public API cleanup and remove the residual compatibility
`hMag` argument by either:

1. concrete `_TM` route, or
2. internalization of `MagnificationAssumptions`.

## 7. Non-goals right now

Do not spend the next theorem sprint on:

1. adding new wrappers;
2. rephrasing the same blocker with more endpoint names;
3. claiming that all-slices infrastructure already closes the final theorem;
4. claiming that removing `hNPDag` alone yields full unconditionality;
5. using archived roadmap notes as the current branch lock.

## 8. Acceptance criteria for “DAG side is closed”

For the DAG side to be honestly called closed in this repository, all of the
following must hold:

1. `ComplexityInterfaces.NP_not_subset_PpolyDAG` is proved internally.
2. The public final theorem no longer takes external `hNPDag`.
3. The repository remains clean under `./scripts/check.sh`.
4. `README.md`, `STATUS.md`, `TODO.md`, and the release/checklist docs are all
   updated consistently.

For the repository to be honestly called **fully unconditional**, add:

5. the public theorem no longer exposes compatibility-only `hMag`;
6. a zero-argument final theorem `P_ne_NP` is derivable in the active tree.
