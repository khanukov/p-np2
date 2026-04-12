# Frontier reduction report

## 1) Chosen path

Chosen path: **Goal A** (honest fallback route with primary DAG-separation focus).

Reason:
- on this branch there is no already-compiled concrete fixed slice `p*` plus concrete
  `GapPartialMCSP_TMWitness p*` object available as a ready witness package;
- therefore a direct zero-arg closure to unconditional `P_ne_NP` through existing `_TM`
  wrappers cannot be completed from current concrete objects alone.

## 2) Exact selected frontier theorem

`Pnp3.Frontier.CoreFrontierObligation` in
`pnp3/Frontier/UnconditionalPneNpFrontier.lean`:

```lean
∃ hMag : MagnificationAssumptions,
  ∃ n : Nat,
    ∃ hn : hMag.antiChecker.asymptotic.N0 ≤ n,
      gapPartialMCSP_supportHalfObligation
        (hMag.antiChecker.asymptotic.pAt n hn)
```

This is the only contentful frontier proposition in the new file.

## 3) Why this is the shortest honest route

- Priority order requested by task was support-half -> blocker -> stable-restriction.
- `dagRouteBSourceBlocker` is definitionally `gapPartialMCSP_supportHalfObligation`,
  so support-half is the minimal source obligation.
- Existing asymptotic final wrappers already reduce this blocker to
  `NP_not_subset_PpolyDAG` without adding new theorem machinery.

## 4) Existing wrappers/theorems used

- `LowerBounds.dagRouteBSourceBlocker` (alias of support-half obligation).
- `Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_blocker`.
- Internal route chain already compiled in repository:
  blocker -> source closure -> stable restriction -> fixed-slice collapse ->
  asymptotic DAG separation.

## 5) What must now be solved in one file

Work only with:
- `pnp3/Frontier/UnconditionalPneNpFrontier.lean`

Single mathematical target:
- prove `CoreFrontierObligation`.

After that, theorems
`frontier_reduces_to_real_NP_not_subset_PpolyDAG`
and
`frontier_reduces_to_real_P_ne_NP`
produce the class-separation object and end-to-end `P_ne_NP` interface
immediately.

## 6) What is still missing for full zero-arg unconditional theorem

Still missing concrete object(s) for the **direct** `_TM` zero-arg closure route:
- concrete `p* : GapPartialMCSPParams`;
- concrete `W : Models.GapPartialMCSP_TMWitness p*`.

(And of course a proved source blocker on that same fixed slice if choosing the `_TM` route.)

## 7) Commands run

- `./scripts/check.sh`
- `lake env lean pnp3/Frontier/UnconditionalPneNpFrontier.lean`
