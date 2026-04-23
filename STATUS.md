# Project Status (current)

Updated: 2026-04-23

Authoritative checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.

## Verified State

- Active `axiom` declarations in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes on the current tree.
- Inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- The repository contains substantial DAG endpoint plumbing, including the
  fixed-slice DAG-to-formula bridge
  `Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`.

## Current Audit Result

There is still **no unconditional in-repo theorem** `P != NP`, and the
current blockers are sharper than the old "remove residual payload" wording.

The active public DAG endpoint is now the honest research-gap boundary:

```text
NP_not_subset_PpolyDAG_final
  (gap : ResearchGapWitness)

P_ne_NP_final
  (gap : ResearchGapWitness)
```

The legacy `hMS`/provider/support-bounds endpoints still compile, but they are
explicitly audit routes in `Magnification.FinalResultAuditRoutes`, not the
public closure boundary.  The falsifiability audit proves:

- `FormulaSupportRestrictionBoundsPartial -> False`
- `FormulaSupportBoundsFromMultiSwitchingContract -> False`
- `MagnificationAssumptions -> False`
- `FormulaSupportBoundsPartial_fromPipeline -> False`
- `MagnificationAssumptions_fromPipeline -> False`

So the legacy support-bounds and multi-switching final routes are vacuous:
they compile, but they route through inconsistent assumptions.

## Fixed-Params Status

Session 67 introduced the stronger contract
`FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb`.

Session 68 established the current honest boundary:

- the Probe 7 singleton-provider attack does not directly port to fixed
  external `ac0` parameters;
- `fixedParams ac0 sb` alone is not currently refuted in the project;
- `fixedParams ac0 sb` plus uniform provenance for every formula witness under
  the same `ac0` reconstructs the old false support-bounds predicate;
- therefore the pair `fixedParams + uniformProvenance` is formally
  inconsistent in the current formalization.

The theorem
`NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance`
is useful as a gap-exposing theorem, not as progress toward an unconditional
claim.  Its assumptions describe the research-level hole.

The single-file boundary for future closure is
`pnp3/Magnification/UnconditionalResearchGap.lean`.  It contains
`ResearchGapWitness` and the compiled bridge
`P_ne_NP_of_researchGap : ResearchGapWitness -> P_ne_NP`; a future
unconditional proof should be localized there by proving
`ComplexityInterfaces.NP_not_subset_PpolyDAG` without using the refuted
support-bounds surfaces.

## What Is Closed

### Inclusion side

- Default inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- Default final wrappers no longer need external inclusion-contract bundles.

### DAG plumbing

- The fixed-slice DAG-to-formula bridge exists.
- Route-B, source-closure, blocker, asymptotic, and `_TM` endpoint wrappers are
  implemented.
- This plumbing is useful for future magnification arguments.

### Fixed-slice no-go status

The historical fixed-slice support-half route is a closed no-go branch under
fixed-slice `PpolyDAG` membership:

- `no_fixedSlice_stableRestriction_of_inPpolyDAG`
- `no_fixedSlice_blocker_of_inPpolyDAG`
- `not_gapPartialMCSP_supportHalfObligation_of_inPpolyDAG`

## What Is Still Open

The remaining blocker is not endpoint plumbing.  It is the missing
non-vacuous source theorem for `ResearchGapWitness`, equivalently
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

A real lower-level route may still come from support/locality mathematics, but
only if it produces DAG separation through a provenance gate that:

1. does not quantify over arbitrary `PpolyFormula` witnesses;
2. cannot be satisfied by truth-table hardwiring or singleton provenance;
3. uses fixed, externally meaningful AC0 parameters;
4. does not combine with an overbroad uniform-provenance assumption to imply
   the old false support-bounds predicate.

That missing theorem is the research-level mathematical gap.  It should be
treated as open, not as a Lean engineering task.

## Repository-Wide Honesty Policy

Any file claiming unconditional `P != NP` is inaccurate until the project has a
non-vacuous replacement for the false support-bounds/multi-switching source and
a zero-argument final theorem that does not depend on external provider
payload.
