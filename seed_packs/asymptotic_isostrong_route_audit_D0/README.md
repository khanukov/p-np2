# Asymptotic iso-strong route audit D0

## Status

OPEN — D0 audit only.

No Lean code.  
No TMVerifier sessions.  
No SourceTheorem.  
No ResearchGapWitness.  
No endpoint.

## Why this exists

PR13 proved:

```text
FormulaCertificateProviderPartial → False
```

This killed the formula-certificate consumer route.

The post-PR13 D0 retarget report found two possible existing non-refuted DAG-side consumers for the canonical asymptotic infrastructure:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`

The report also identified `AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym` as a possible upstream route into the promise-YES certificate route.

That earlier result was only retarget feasibility.  It was not a non-vacuity result.  This seed pack exists to audit whether these route surfaces are genuinely non-vacuous and whether they are safe from hardwiring before any TMVerifier sessions resume.

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
- No source edits.
- No JSONL edits.
- No NoGoLog edits.
- No ResearchGapWitness.
- No SourceTheorem.
- No `gap_from`.
- No endpoint.
- No P≠NP claim.
- No TMVerifier session work.

## Allowed scope

Only the seed pack skeleton files are in scope:

- `seed_packs/asymptotic_isostrong_route_audit_D0/README.md`
- `seed_packs/asymptotic_isostrong_route_audit_D0/WORKER_PROMPT_D0.md`
- `seed_packs/asymptotic_isostrong_route_audit_D0/reports/.gitkeep`
- `seed_packs/asymptotic_isostrong_route_audit_D0/failures/.gitkeep`
