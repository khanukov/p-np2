# Asymptotic iso-strong route audit D0

## 1. Status

**OPEN — D0 audit only.**

No Lean code.  
No TMVerifier sessions.  
No `SourceTheorem`.  
No `ResearchGapWitness`.  
No endpoint.

## 2. Why this exists

PR13 proved:

```text
FormulaCertificateProviderPartial → False
```

This killed the formula-certificate consumer route.

The post-PR13 D0 retarget report found two possible existing consumers for
canonical asymptotic infrastructure on the non-refuted DAG side:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`

It also identified `AsymptoticPromiseYesWeakRouteEventually` as a possible
upstream surface to inspect.

That retarget was only a feasibility recommendation.  It did not prove that the
surviving route surfaces are non-vacuous, safe from hardwiring, or suitable as a
next formal target.  This seed pack exists to audit those existing route
surfaces before any TMVerifier sessions resume.

## 3. Audit targets

The D0 report must audit these route surfaces and their endpoint behavior:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym`
- Their final endpoints with `AntiChecker`

## 4. Central questions

A. Is `hInDag` trivially dischargeable in-repo?

B. Is the route vacuous for `canonicalAsymptoticSpec`?

C. Does a DAG-side truth-table hardwiring twin exist?

D. Does a syntax/rewrite/normalization attack analogue exist?

E. Is `PromiseYesSubcubeCertificateAt` nontrivial at canonical params?

F. Which route, if any, should be selected as next formal target?

## 5. Allowed outcome

One markdown report.

## 6. Possible verdicts

- `GREEN_EXISTING_ROUTE_NONVACUOUS`
- `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS`
- `RED_ROUTE_VACUOUS_OR_HARDWIRED`
- `INCONCLUSIVE_NEEDS_LEAN_PROBE`

## 7. Forbidden scope

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

## 8. Allowed scope

Only the seed pack skeleton files are in scope:

- `seed_packs/asymptotic_isostrong_route_audit_D0/README.md`
- `seed_packs/asymptotic_isostrong_route_audit_D0/WORKER_PROMPT_D0.md`
- `seed_packs/asymptotic_isostrong_route_audit_D0/reports/.gitkeep`
- `seed_packs/asymptotic_isostrong_route_audit_D0/failures/.gitkeep`
