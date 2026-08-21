# P vs NP: Lean Formalization (Honest Status)

Status date: 2026-08-21.

`STATUS.md` is the authoritative, most-recently-updated snapshot; this README is a
stable high-level overview and may lag it by weeks or months.  Where the two differ,
`STATUS.md` wins.

Canonical checklist for unconditional readiness:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.

## What This Project Is

This repository contains two active Lean 4 formalization tracks.

`pnp3/` — a magnification route around Partial MCSP:

`SAL -> Covering/Lower Bounds -> anti-checker -> magnification -> final wrappers`.

`pnp4/` — an algorithms-to-lower-bounds / compression-magnification track.  Per
`AGENTS.md`, pnp4 carries the P-vs-NP **mainline**: only work reducing
`SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource` counts as mainline
progress.  Its restricted `AC0[p]` / formula / local-PRG / coin-problem lower bounds are
an explicit side track.  See `pnp4/README.md`.

Both tracks terminate at the same target,
`ComplexityInterfaces.NP_not_subset_PpolyDAG`, and neither closes it.

Historical material under `archive/` is kept for provenance only and must not be
treated as the status source for the current branch.

## Variant Boundary

Active `pnp3/` development uses **Partial MCSP** (`GapPartialMCSP*` names).

- Working model: `pnp3/Models/Model_PartialMCSP.lean`.
- Active language/promise names: `gapPartialMCSP_Language`,
  `GapPartialMCSPPromise`.
- Legacy total-table / older MCSP variants are historical unless explicitly
  linked from active status docs.

## Current Verified State

- `pnp3/` and `pnp4/` build and `./scripts/check.sh` passes on the current tree.
- Active project-local `axiom` declarations: `0` in `pnp3/`, `0` in `pnp4/`
  (both enforced by `scripts/check.sh`).
- Active `sorry/admit`: `0` in `pnp3/`, `0` in `pnp4/`.
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

Beyond the formula-side refutation above, the **canonical asymptotic track**
(the iso-strong and promise-YES route family) is now also formally closed at
the conclusion level.  The kernel-checked, in-build witness is
`isoStrong_conclusion_negative_general` in
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`; see `STATUS.md` for the full
audit chain.  This does not prove `P != NP`; it rules out that route family.

The former pnp3 fixed-slice AC0 endpoint is a deprecated audit quarantine
(`pnp3/LowerBounds/AC0_GapMCSP.lean`).  Its enriched `SmallAC0Solver_Partial` package is
inconsistent from `params` and `easyData` alone, before solver correctness is used
(`false_of_smallAC0Params_and_easyFamilyData`), so the historical `in_AC0` / `not_in_AC0`
names are not a standard AC0 lower bound and not P-vs-NP progress.

On the pnp4 side there is a machine-checked **conditional** chain from a concrete
tree-MCSP search lower bound to `NP_not_subset_PpolyDAG`
(`NP_not_subset_PpolyDAG_treePoly`).  It proves neither `P != NP` nor
`NP_not_subset_PpolyDAG`: at a concrete polynomial threshold it still depends on exactly
two unproved hypotheses.  See `STATUS.md` and
`pnp4/Pnp4/Frontier/ContractExpansion/README.md`.

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
- `AGENTS.md` - mainline / side-track / infrastructure classification policy.
- `pnp4/README.md` and
  `pnp4/Pnp4/Frontier/ContractExpansion/README.md` - pnp4 track and the
  proved-vs-open breakdown of its conditional chain.

## Wording Policy

Until the checklist is fully closed, any statement of `P != NP` in this
repository must explicitly say that the current final theorem surface remains
conditional and that the support-bounds source theorem is still open.
