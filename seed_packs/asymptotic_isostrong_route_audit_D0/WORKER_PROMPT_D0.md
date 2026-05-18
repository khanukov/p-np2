# Worker prompt — asymptotic iso-strong / promise-YES route audit D0

## Branch

`main`

## Task

Create and execute a D0-only audit report for the existing asymptotic
iso-strong / promise-YES route surfaces.

This seed pack is markdown-only.  Do not write Lean code.

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

But that recommendation was only retarget feasibility, not non-vacuity.

This seed pack audits those existing route surfaces before any TMVerifier
sessions resume.

## Required reading

Read these files before writing the D0 report:

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

If any required reading path has moved or is absent, record that fact in the
report instead of guessing its contents.

## Audit targets

Audit exactly these existing route surfaces and their endpoint behavior:

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

## Output file

Create exactly one report file:

```text
seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_isostrong_route_audit_<HANDLE>.md
```

Replace `<HANDLE>` with your worker handle.

## Required report sections

The report must contain all of these sections:

1. Executive verdict.
2. Required-reading inventory.
3. Route-surface inventory.
4. `hInDag` discharge audit.
5. Vacuity audit for `canonicalAsymptoticSpec`.
6. DAG truth-table hardwiring audit.
7. Syntax / rewrite / normalization attack audit.
8. `PromiseYesSubcubeCertificateAt` nontriviality audit.
9. Endpoint-with-`AntiChecker` audit.
10. Recommended next formal target, if any.
11. Verdict.

## Possible verdicts

End with exactly one of:

- `GREEN_EXISTING_ROUTE_NONVACUOUS`
- `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS`
- `RED_ROUTE_VACUOUS_OR_HARDWIRED`
- `INCONCLUSIVE_NEEDS_LEAN_PROBE`

## Forbidden scope

No Lean code.  
No source edits.  
No JSONL edits.  
No NoGoLog edits.  
No `ResearchGapWitness`.  
No `SourceTheorem`.  
No `gap_from`.  
No endpoint.  
No P≠NP claim.  
No TMVerifier session work.

## Allowed scope

Only write the D0 report under this seed pack's `reports/` directory.  Do not
edit existing source files, generated logs, JSONL files, NoGoLog files, Lean
modules, or final endpoints.

## Commands

Run:

```bash
./scripts/check.sh
```

If the check fails for an environment reason, record the exact command, exit
status, and relevant output in the report.
