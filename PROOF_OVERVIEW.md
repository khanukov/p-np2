# Proof Overview (Auditor Guide)

Updated: 2026-04-03

This file is the short auditor-oriented map of the active proof route in the
current repository state.

Canonical unconditional checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current interim release posture:
`RELEASE_RC.md`.

## 1. Pipeline shape

Active code path remains:

`SAL -> Covering/Lower Bounds -> anti-checker -> magnification -> DAG final wrappers`.

Final theorem interfaces are centralized in
`pnp3/Magnification/FinalResultCore.lean`
(with compatibility import path `pnp3/Magnification/FinalResult.lean`).

## 2. Final theorem ladder in code

The active ladder now has several honest DAG-facing layers.

### Default compatibility surface

1. `NP_not_subset_PpolyFormula_final*`
2. `NP_not_subset_PpolyReal_final*`
3. `P_ne_NP_final*`

### Additional fixed-slice / asymptotic DAG surfaces

1. `NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse`
2. `NP_not_subset_PpolyDAG_final_of_asymptotic_dag_stableRestriction`
3. `NP_not_subset_PpolyDAG_final_of_asymptotic_sourceClosure`
4. `NP_not_subset_PpolyDAG_final_of_asymptotic_blocker`
5. companion `P_ne_NP_final_of_*` wrappers for the same fixed-slice routes

### Concrete fixed-slice `_TM` DAG surfaces

1. `NP_not_subset_PpolyDAG_final_of_blocker_TM`
2. `P_ne_NP_final_of_blocker_TM`
3. related `_TM` wrappers from stable restriction / source closure /
   support-bounds bridges

## 3. Current explicit boundary assumptions

The public default theorem is still:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : NP_not_subset_PpolyDAG)
```

Interpretation:

1. `hNPDag` is the real remaining DAG-separation blocker.
2. `hMag` is currently compatibility context and is not consumed by the
   implementation of `P_ne_NP_final`.

## 4. What is closed

Closed in the active tree:

1. buildable active route and final wrappers;
2. axiom/sorry hygiene for active `pnp3/`;
3. inclusion-side internalization;
4. asymptotic fixed-slice collapse wrappers;
5. canonical witness-density hardwire coverage;
6. support-half family fallback closure;
7. current audit/regression test suite.

## 5. What is open

Still open:

1. an internal theorem `ComplexityInterfaces.NP_not_subset_PpolyDAG`;
2. a zero-argument public theorem `P_ne_NP`;
3. the fixed-slice source theorem needed to feed the new asymptotic collapse
   wrappers;
4. or, alternatively, a standalone concrete-slice `_TM` route that bypasses
   `hMag` entirely.

## 6. Current recommended audit reading

If the goal is to understand the real blocker rather than the packaging:

1. `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
2. `pnp3/LowerBounds/DAGUnconditionalBlocker.lean`
3. `pnp3/LowerBounds/AsymptoticDAGBarrier.lean`
4. `pnp3/Magnification/FinalResultCore.lean`

## 7. Minimal verification script

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean; do
  lake env lean "$f"
done
rg -n "^theorem P_ne_NP_final|^theorem NP_not_subset_PpolyDAG_final_of_|^theorem P_ne_NP_final_of_" \
  pnp3/Magnification/FinalResultCore.lean
```

## 8. Documentation policy

Use these files as the active source of truth:

1. `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`
2. `STATUS.md`
3. `TODO.md`
4. `AXIOMS_FINAL_LIST.md`

Historical notes in `archive/` remain non-authoritative.
