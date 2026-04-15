# P vs NP: Lean Formalization (Honest Status)

Status date: 2026-04-03.

Canonical checklist for unconditional readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.

## What This Project Is

This repository contains a Lean 4 formalization of a route of the form

`SAL -> Covering/Lower Bounds -> anti-checker -> magnification -> final wrappers`.

The active code lives in `pnp3/`. Historical material under `archive/` is kept
for provenance only and must not be treated as the status source for the
current branch.

## Variant Boundary

Active `pnp3/` development uses **Partial MCSP** (`GapPartialMCSP*` names).

- Working model: `pnp3/Models/Model_PartialMCSP.lean`.
- Active language/promise names: `gapPartialMCSP_Language`,
  `GapPartialMCSPPromise`.
- Legacy total-table / older MCSP variants are historical unless explicitly
  linked from active status docs.

## Current Verified State

- `pnp3/` builds and `./scripts/check.sh` passes on the current tree.
- Active project-local `axiom` declarations in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- Final compatibility entrypoint lives in `pnp3/Magnification/FinalResult.lean`,
  while the active implementation surface is in
  `pnp3/Magnification/FinalResultCore.lean`
  (split into `FinalResultMainline/WeakRoutes/LegacyTM`).
- Inclusion is already internalized:
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- The DAG side now has substantially more compiled surface area:
  asymptotic fixed-slice collapse wrappers,
  Route-B/source-closure/blocker wrappers,
  support-half accepted-family fallback wrappers,
  and canonical witness-density / witness-transfer compiler infrastructure.

## What Is Not Yet Proved

There is still **no unconditional in-repo theorem** `P ≠ NP`.

The public default final theorem is still:

```text
P_ne_NP_final
  (hMag : MagnificationAssumptions)
```

Two important facts about that signature:

1. External class-level DAG separation `hNPDag` is no longer required by the
   default final theorem.
2. Internal DAG separation is now derived inside
   `NP_not_subset_PpolyDAG_final`.
3. `hMag` is still present as the remaining compatibility context.

So the repository is no longer blocked at the DAG-separation layer, but it is
still not unconditional at the final zero-argument API layer.

## What Changed Recently

Recent code now exposes the following additional honest routes:

- a fixed-slice DAG-to-formula bridge
  `Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`;
- a canonical internal DAG final `NP_not_subset_PpolyDAG_final`;
- a one-argument default final theorem
  `P_ne_NP_final (hMag : MagnificationAssumptions)`;
- asymptotic fixed-slice DAG finals:
  `NP_not_subset_PpolyDAG_final_of_asymptotic_fixedSliceCollapse`,
  `..._of_asymptotic_dag_stableRestriction`,
  `..._of_asymptotic_sourceClosure`,
  `..._of_asymptotic_blocker`,
  plus companion `P_ne_NP_final_of_*` wrappers;
- fixed-slice `_TM` finals from concrete DAG-side witnesses:
  `NP_not_subset_PpolyDAG_final_of_blocker_TM`,
  `P_ne_NP_final_of_blocker_TM`, and related source-closure /
  stable-restriction wrappers;
- support-half fallback closure:
  `noSmallDAG_of_supportHalfBoundFamily` and
  `NP_not_subset_PpolyDAG_surface_of_supportHalfBoundFamily`;
- canonical witness-density hardwire coverage and all-slices compilers in
  `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`.

This means the repository is no longer blocked on endpoint plumbing or on an
external DAG payload. The remaining debt is formula-side / magnification-side
theorem closure.

## Current Best Next Steps

There is now one remaining closure goal.

### Goal: reach a truly zero-argument unconditional theorem

The DAG side is already internalized. Full unconditionality now requires
eliminating the remaining public `hMag` argument.

The shortest credible ways to do that are:

1. separately internalize the current magnification-assumption package, so
   `NP_not_subset_PpolyFormula_final` no longer takes `hMag`; or
2. bypass the package-shaped public surface with a zero-argument final route.

## Verification

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean; do
  lake env lean "$f"
done
```

Also check:

```bash
UNCONDITIONAL=1 ./scripts/check.sh
```

At the current tree state this fails only because
`NP_not_subset_PpolyFormula_final` still depends on
`MagnificationAssumptions`.

## Primary Documents

- `STATUS.md` - authoritative current snapshot.
- `TODO.md` - remaining execution order.
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` - exact closure checklist.
- `PROOF_OVERVIEW.md` - auditor-oriented route map.
- `RELEASE_RC.md` - release posture and wording guardrail.
- `FAQ.md` - short reviewer-facing clarifications.
- `AXIOMS_FINAL_LIST.md` - axiom/sorry hygiene only.

## Wording Policy

Until the checklist is fully closed, any statement of `P ≠ NP` in this
repository must explicitly say that the current final theorem surface remains
conditional.
