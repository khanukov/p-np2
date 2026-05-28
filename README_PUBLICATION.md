# Release landing page

This is the publication-facing entry point for the PNP3 release.

- Release type: **RC / framework milestone**, not a final unconditional claim.
- Status date: 2026-05-28.
- Source of truth for release wording: `RELEASE_RC.md`.
- Source of truth for closure progress: `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.

## Claim matrix

| Claim                                                                 | Status                                                       |
|-----------------------------------------------------------------------|--------------------------------------------------------------|
| Active `pnp3/` has no project-local axioms and no `sorry`/`admit`     | Verified by `scripts/check.sh` policy                        |
| `P_subset_PpolyDAG` internalized                                      | Proved, but coarse polynomial-size inclusion                 |
| `ResearchGapWitness` → `P_ne_NP_final`                                | Proved conditional bridge                                    |
| Old support-bounds / multi-switching route                            | Formally refuted; retained only as audit / compatibility     |
| `FormulaSupportBoundsPartial_fromPipeline_fixedParams`                | Candidate contract shape, not a proved source theorem        |
| Unconditional `P != NP`                                               | **Not claimed**                                              |

## Public closure boundary

The current public default endpoints (in
`pnp3/Magnification/UnconditionalResearchGap.lean`) are:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
P_ne_NP_final               (gap : ResearchGapWitness)
```

The only mathematical input is
`ResearchGapWitness.dagSeparation : NP_not_subset_PpolyDAG`.  Legacy
`hMag` / `hMS` / support-bounds / multi-switching / provider entry points
are retained only as explicit audit / compatibility wrappers; their source
predicates are formally refuted by the falsifiability audit.

## What this release does not include

1. An unconditional in-repo theorem `P != NP`.
2. A non-vacuous proof of the formula-side support / locality source
   theorem.
3. A proof that `FormulaSupportBoundsPartial_fromPipeline_fixedParams` is
   realizable for realistic AC0 parameters.
4. A zero-argument final theorem with no external research payload.

## How to verify

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

## Where to read next

| Question                                | File                                         |
|-----------------------------------------|----------------------------------------------|
| What is the project, in two pages?      | `README.md`                                  |
| What is closed and what is open?        | `STATUS.md`                                  |
| What blocks unconditional closure?      | `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`         |
| Route map for auditors                  | `PROOF_OVERVIEW.md`                          |
| Common questions                        | `FAQ.md`                                     |
| Verified vs. not-claimed claim table    | `TECHNICAL_CLAIMS.md`                        |
| Axiom / `sorry` hygiene only            | `AXIOMS_FINAL_LIST.md`                       |
| Detailed Russian frontier FAQ           | `pnp3/Docs/Unconditionality_FAQ_ru.md`       |
| Route policy lock                       | `pnp3/Docs/CLOSURE_ROUTE_POLICY.md`          |
| Release wording guardrail               | `RELEASE_RC.md`                              |
