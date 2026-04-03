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
- Final entrypoints live in `pnp3/Magnification/FinalResult.lean`.
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
  (hNPDag : NP_not_subset_PpolyDAG)
```

Two important facts about that signature:

1. `hNPDag` is the real logical DAG-side blocker.
2. `hMag` is still present as compatibility context, but the current default
   implementation does not consume it.

So the repository is not yet unconditional either at the DAG-separation layer
or at the final zero-argument API layer.

## What Changed Recently

Recent code now exposes the following additional honest routes:

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

This means the repository is no longer blocked on endpoint plumbing.
The remaining debt is theorem-level.

## Current Best Next Steps

There are two distinct closure goals.

### Goal A: remove external `hNPDag` from the current `hMag`-based final path

The fastest honest route is currently:

1. choose one fixed slice
   `p* := hMag.antiChecker.asymptotic.pAt n hn`;
2. prove one fixed-slice DAG source theorem on `p*`, preferably
   `gapPartialMCSP_supportHalfObligation p*`,
   or equivalently `dagRouteBSourceBlocker p*`,
   or otherwise `dag_stableRestriction_producer p*`;
3. feed that theorem into the already compiled asymptotic wrappers.

### Goal B: reach a truly zero-argument unconditional theorem

Removing `hNPDag` is not enough by itself. Full unconditionality still requires
eliminating the remaining public `hMag` argument too.

The shortest credible ways to do that are:

1. bypass `hMag` completely with a concrete fixed slice `p*`, a concrete
   `GapPartialMCSP_TMWitness p*`, and a fixed-slice blocker fed into the
   existing `_TM` final wrappers; or
2. separately internalize the current magnification-assumption package.

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
