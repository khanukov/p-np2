# P vs NP: Lean Formalization (Honest Status)

Status date: 2026-04-22.

Canonical checklist for unconditional readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.

## What This Project Is

This repository contains a Lean 4 formalization framework for a magnification
route around Partial MCSP:

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
- Inclusion is internalized:
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- DAG endpoint plumbing is substantial, including the fixed-slice
  `PpolyDAG -> PpolyFormula` bridge and final wrappers.

## Current Audit Result

There is still **no unconditional in-repo theorem** `P != NP`.

The earlier support-bounds route was not merely incomplete.  It was formally
refuted:

- `FormulaSupportRestrictionBoundsPartial -> False`
- `FormulaSupportBoundsFromMultiSwitchingContract -> False`
- `MagnificationAssumptions -> False`
- `FormulaSupportBoundsPartial_fromPipeline -> False`

The root cause is fixed-slice truth-table hardwiring.  The old predicates were
strong enough to apply to arbitrary polynomial-size formula witnesses, including
hardwired formulas whose support is all variables.

## Fixed-Params Candidate

The current nontrivial candidate shape is:

```text
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

It fixes AC0 parameters externally, so the known singleton-provider attack does
not directly port.  But it is not a proved lower-bound theorem.  Also,
`fixedParams + uniformProvenance` reconstructs the old false support-bounds
predicate and is therefore inconsistent as currently stated.

The theorem
`NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance` exposes
this research gap.  It does not close it.

The one-file closure boundary is
`pnp3/Magnification/UnconditionalResearchGap.lean`.  It defines
`ResearchGapWitness` and proves the conditional bridge from that witness to
`P != NP`.

## What This Means

The repository is useful as a formal framework and audit harness for future
magnification attacks.  It does not currently prove `P != NP`, and the
remaining gap is mathematical: a non-vacuous fixed-params support/locality
source theorem that cannot be satisfied by truth-table hardwiring or singleton
provenance.

## Verification

```bash
./scripts/check.sh
for f in pnp3/Tests/AxiomsAudit.lean \
         pnp3/Tests/BarrierAudit.lean \
         pnp3/Tests/BarrierBypassAudit.lean \
         pnp3/Tests/BridgeLocalityRegression.lean \
         pnp3/Tests/WeakRouteSurfaceTests.lean \
         pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean; do
  lake env lean "$f"
done
```

## Primary Documents

- `STATUS.md` - authoritative current snapshot.
- `TODO.md` - remaining execution order.
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md` - exact closure checklist.
- `pnp3/Magnification/UnconditionalResearchGap.lean` - single-file remaining
  research gap boundary.
- `RELEASE_RC.md` - release posture and wording guardrail.
- `AXIOMS_FINAL_LIST.md` - axiom/sorry hygiene only.

## Wording Policy

Until the checklist is fully closed, any statement of `P != NP` in this
repository must explicitly say that the current final theorem surface remains
conditional and that the support-bounds source theorem is still open.
