# Worker prompt — asymptotic iso-strong route audit D0

## Branch

`main`

## Task

Audit the existing asymptotic iso-strong / promise-YES route surfaces for the canonical D0 retarget.

This is markdown-only.  Do not write Lean code.

## Classification

D0 route audit.  This is not a SourceTheorem, not a `ResearchGapWitness`, not an endpoint, and not a P≠NP claim.  Report it only as an audit of existing route surfaces before any TMVerifier sessions resume.

## Context

PR13 proved:

```text
FormulaCertificateProviderPartial → False
```

This killed the formula-certificate consumer route.

The post-PR13 D0 retarget report recommended retargeting canonical asymptotic infrastructure to existing non-refuted DAG-side consumers:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
- possibly `AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym` as upstream

That recommendation established retarget feasibility only.  It did not establish non-vacuity.

This D0 audit must determine whether those existing route surfaces are non-vacuous and hardwiring-safe enough to justify later formal work.

## Required reading

Read before writing the report:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md`
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
- `pnp3/RefutedPredicates/Registry.lean`
- `STATUS.md`
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`
- `pnp3/Tests/CanonicalIntegrationTests.lean`
- `pnp3/Magnification/FinalResultMainline.lean`
- `pnp3/Magnification/FinalResultWeakRoutes.lean`
- `pnp3/Tests/WeakRouteSurfaceTests.lean`

## Audit targets

Audit these route surfaces at the canonical asymptotic data:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym`
- Their final endpoints with `AntiChecker`

## Central questions

Answer all of the following explicitly:

A. Is `hInDag` trivially dischargeable in-repo?

B. Is the route vacuous for `canonicalAsymptoticSpec`?

C. Does a DAG-side truth-table hardwiring twin exist?

D. Does a syntax/rewrite/normalization attack analogue exist?

E. Is `PromiseYesSubcubeCertificateAt` nontrivial at canonical params?

F. Which route, if any, should be selected as next formal target?

## Deliverable

Create exactly one markdown report:

```text
seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_isostrong_route_audit_<HANDLE>.md
```

Use your own handle in `<HANDLE>`.

## Report requirements

The report must include:

1. **Verdict** — choose exactly one:
   - `GREEN_EXISTING_ROUTE_NONVACUOUS`
   - `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS`
   - `RED_ROUTE_VACUOUS_OR_HARDWIRED`
   - `INCONCLUSIVE_NEEDS_LEAN_PROBE`
2. **Evidence from required reading** — cite the exact existing route definitions, canonical infrastructure, PR13 refutation surface, and integration tests that support the verdict.
3. **Non-vacuity audit** — analyze `hInDag`, canonical parameters, and whether any route can be discharged by an already-known false/refuted predicate or by an in-repo trivial construction.
4. **Hardwiring audit** — compare the route shape against the formula-certificate failure mode and search for a DAG-side truth-table / singleton / hardwired witness analogue.
5. **Promise-YES certificate audit** — assess whether `PromiseYesSubcubeCertificateAt` is substantively nontrivial at the canonical parameters and whether the weak eventual route genuinely strengthens into the certificate route.
6. **Recommendation** — identify which route, if any, should be selected as the next formal target, or explain why the next step must be a targeted Lean probe instead.
7. **Scope statement** — explicitly state that the report made no Lean changes, no SourceTheorem, no `ResearchGapWitness`, no endpoint, no P≠NP claim, and no TMVerifier session progress.

## Forbidden scope

- No Lean code.
- No source edits.
- No JSONL edits.
- No NoGoLog edits.
- No ResearchGapWitness.
- No SourceTheorem.
- No `gap_from`.
- No endpoint.
- No P≠NP claim.
- No TMVerifier session work.
- Do not claim this D0 audit itself proves non-vacuity unless the evidence supports the selected verdict.
- Do not introduce new files outside the single report unless recording a failure note under `failures/` because the D0 report could not be completed.

## Allowed scope

- One D0 markdown report under `reports/`.
- If the report cannot be completed, one markdown failure note under `failures/` explaining why.

## Commands

Run:

```bash
./scripts/check.sh
```

## Output format

End your response with:

```text
Task: asymptotic_isostrong_route_audit_D0 skeleton
Commit before: <hash>
Commit after: <hash>
Changed files:
- <path>
D0 only: yes/no
Commands run:
- <command> => <result>
Scope violations: <none or list>
```
