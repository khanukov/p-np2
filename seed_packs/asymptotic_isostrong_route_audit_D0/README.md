# asymptotic_isostrong_route_audit_D0 — D0 route-surface audit

## 1. Status

**OPEN — D0 audit only.**

No Lean code.
No TMVerifier sessions.
No `SourceTheorem`.
No `ResearchGapWitness`.
No endpoint.

This seed pack is markdown-only. It is an audit scaffold for deciding whether
existing canonical asymptotic DAG-side route surfaces are non-vacuous and safe
enough to target after PR13.

## 2. Why this exists

PR13 proved:

```text
FormulaCertificateProviderPartial → False
```

This killed the formula-certificate consumer route.

The post-PR13 D0 retarget report found two possible existing non-refuted
DAG-side consumers for canonical asymptotic infrastructure:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`

It also identified `AsymptoticPromiseYesWeakRouteEventually
canonicalAsymptoticHAsym` as a possible upstream surface.

That retarget was only a feasibility result. It did **not** establish
non-vacuity, hardwiring resistance, or safety against syntax/rewrite attacks.
This D0 seed pack exists to audit those route surfaces before any TMVerifier
sessions resume.

## 3. Audit targets

D0 workers must audit these existing route surfaces:

- `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
- `AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym`
- their final endpoints with `AntiChecker`

The audit should treat the route surfaces as read-only context and should not
promote, weaken, rename, or rewrite them.

## 4. Central questions

A. Is `hInDag` trivially dischargeable in-repo?

B. Is the route vacuous for `canonicalAsymptoticSpec`?

C. Does a DAG-side truth-table hardwiring twin exist?

D. Does a syntax/rewrite/normalization attack analogue exist?

E. Is `PromiseYesSubcubeCertificateAt` nontrivial at canonical params?

F. Which route, if any, should be selected as next formal target?

## 5. Allowed outcome

The allowed D0 outcome is one markdown report under `reports/`.

A suggested filename is:

```text
seed_packs/asymptotic_isostrong_route_audit_D0/reports/D0_asymptotic_isostrong_route_audit_<HANDLE>.md
```

The report must answer the central questions and end with exactly one verdict
from the list below.

## 6. Possible verdicts

- `GREEN_EXISTING_ROUTE_NONVACUOUS`
- `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS`
- `RED_ROUTE_VACUOUS_OR_HARDWIRED`
- `INCONCLUSIVE_NEEDS_LEAN_PROBE`

A green verdict is only a recommendation for the operator to select a later
formal target. It is not permission to write Lean code or start TMVerifier work
inside this D0 seed pack.

## 7. Forbidden scope

No Lean code.
No source edits.
No JSONL edits.
No NoGoLog edits.
No `ResearchGapWitness`.
No `SourceTheorem`.
No `gap_from`.
No endpoint.
No `P≠NP` claim.
No TMVerifier session work.

## 8. Allowed scope

Only this seed pack's skeleton files may be created or edited:

- `seed_packs/asymptotic_isostrong_route_audit_D0/README.md`
- `seed_packs/asymptotic_isostrong_route_audit_D0/WORKER_PROMPT_D0.md`
- `seed_packs/asymptotic_isostrong_route_audit_D0/reports/.gitkeep`
- `seed_packs/asymptotic_isostrong_route_audit_D0/failures/.gitkeep`
