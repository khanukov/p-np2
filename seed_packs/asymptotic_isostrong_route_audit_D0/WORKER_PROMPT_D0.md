# Worker prompt: asymptotic_isostrong_route_audit_D0

## Branch

`main`

## Task

Create a D0-only audit report for the asymptotic iso-strong / promise-YES route
surfaces.

This is markdown-only.

Do not write Lean code.

## Context

PR13 proved:

```text
FormulaCertificateProviderPartial → False
```

This killed the formula-certificate consumer route.

The post-PR13 retarget D0 report recommended retargeting canonical asymptotic
infrastructure to existing non-refuted DAG-side consumers:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
- possibly `AsymptoticPromiseYesWeakRouteEventually` as upstream

That recommendation was only retarget feasibility, not non-vacuity.  This seed
pack audits those existing route surfaces before any TMVerifier sessions resume.

## Required reading

Read:

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

## Goal

Produce exactly one markdown report in:

```text
seed_packs/asymptotic_isostrong_route_audit_D0/reports/
```

The report must audit the existing route surfaces for non-vacuity and
hardwiring safety.  It must not claim an endpoint, a source theorem, a research
gap witness, or P≠NP.

## Audit targets

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym`
- Their final endpoints with `AntiChecker`

## Central questions

A. Is `hInDag` trivially dischargeable in-repo?

B. Is the route vacuous for `canonicalAsymptoticSpec`?

C. Does a DAG-side truth-table hardwiring twin exist?

D. Does a syntax/rewrite/normalization attack analogue exist?

E. Is `PromiseYesSubcubeCertificateAt` nontrivial at canonical params?

F. Which route, if any, should be selected as next formal target?

## Allowed outcome

One markdown report.

## Possible verdicts

- `GREEN_EXISTING_ROUTE_NONVACUOUS`
- `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS`
- `RED_ROUTE_VACUOUS_OR_HARDWIRED`
- `INCONCLUSIVE_NEEDS_LEAN_PROBE`

## Forbidden scope

- No Lean code.
- No source edits outside this seed pack's report file.
- No JSONL edits.
- No NoGoLog edits.
- No `ResearchGapWitness`.
- No `SourceTheorem`.
- No `gap_from`.
- No endpoint.
- No P≠NP claim.
- No TMVerifier session work.

## Commands

Run:

```bash
./scripts/check.sh
```

## Required output format

```text
Task: asymptotic_isostrong_route_audit_D0 report
Commit before:
Commit after:
Changed files:
D0 only: yes/no
Commands run:
Scope violations:
```
