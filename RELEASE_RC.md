# Release Plan (RC): 2026-05-28

This document defines the recommended release posture for the current state.

## Release Type

`RC / framework milestone`, not a final unconditional claim.

## What Is Included

1. Default inclusion side is internalized through
   `Simulation.proved_P_subset_PpolyDAG_internal`.
2. Active tree remains axiom-clean (`axiom = 0`, `sorry/admit = 0` in
   `pnp3/`).
3. DAG endpoint infrastructure is present: fixed-slice DAG-to-formula bridge,
   asymptotic wrappers, `_TM` wrappers, Route-B/source-closure/blocker
   surfaces, and support-half fallback surfaces.
4. The falsifiability audit is now explicit:
   - old support-bounds route is ex-falso;
   - old multi-switching contract is ex-falso;
   - the first pipeline-aware replacement is ex-falso;
   - fixedParams blocks the known singleton-provider attack but remains a
     candidate contract, not a proved theorem.
5. The gap-exposing theorem
   `NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance`
   makes the research-level assumptions explicit.
6. The single-file frontier module
   `pnp3/Magnification/UnconditionalResearchGap.lean` records the remaining
   gap as `ResearchGapWitness` and provides the conditional bridge to
   `P != NP`.

## What Is Not Included

1. Unconditional in-repo theorem `P != NP`.
2. A non-vacuous proof of the formula-side support/locality source theorem.
3. A proof that fixedParams is realizable for realistic AC0 parameters.
4. A zero-argument final theorem with no external provider payload.

## Mandatory Public Wording

Use wording equivalent to:

1. "This release provides a Lean framework and falsifiability audit for a
   magnification route."
2. "The legacy support-bounds and multi-switching assumptions were found to be
   inconsistent in the formalization."
3. "The fixedParams contract is a candidate shape for future work, not a
   completed lower-bound theorem."
4. "Final `P != NP` remains conditional; no unconditional claim is made."

Avoid wording that says:

1. that DAG separation is fully solved, without mentioning that the legacy
   route still relies on formally refuted formula-side support-bounds
   assumptions.
2. that only API cleanup or wrapper bookkeeping remains.
3. that the remaining work is just Lean formalization.

## Release Checklist

Run and archive outputs for:

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

Confirm docs are aligned (matches the public-doc allowlist enforced by
`scripts/check.sh` route-policy step):

- `README.md`
- `README_PUBLICATION.md`
- `STATUS.md`
- `TODO.md`
- `FAQ.md`
- `PROOF_OVERVIEW.md`
- `TECHNICAL_CLAIMS.md`
- `AXIOMS_FINAL_LIST.md`
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`
- `RELEASE_RC.md` (this file)
- `pnp3/Docs/CLOSURE_ROUTE_POLICY.md`
- `pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`
- `pnp3/Docs/Simulation_FineGrained_Status.md`
- `pnp3/Docs/Research_Method_Boundary.md`
- `pnp3/Docs/Unconditionality_FAQ_ru.md`

## Post-RC Research Plan

1. Treat `FormulaSupportBoundsPartial_fromPipeline_fixedParams` as a candidate
   contract only.
2. Audit every proposed replacement source against truth-table hardwiring.
3. Do not wire a new source into final theorems until it has a falsifiability
   probe showing it does not imply the old false predicate.
4. Keep independent formalization milestones separate from `P != NP` claims.
