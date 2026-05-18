# Worker prompt — asymptotic_isostrong_route_audit_D0 skeleton

## Branch

`main`

## Task

Create a D0-only seed pack skeleton for the asymptotic iso-strong /
promise-YES route audit.

Seed pack:

```text
seed_packs/asymptotic_isostrong_route_audit_D0/
```

This is markdown-only. Do not write Lean code.

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

But that was only retarget feasibility, not non-vacuity.

This seed pack audits those existing route surfaces before any TMVerifier
sessions resume.

## Required reading

Read:

- `RESEARCH_CONSTITUTION.md`
- Post-PR13 retarget report:
  `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md`
- PR13:
  - `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
  - `pnp3/RefutedPredicates/Registry.lean`
  - `STATUS.md`
- Canonical infrastructure:
  - `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  - `pnp3/Magnification/CanonicalAsymptoticDecider.lean`
  - `pnp3/Tests/CanonicalIntegrationTests.lean`
- Route surfaces:
  - `pnp3/Magnification/FinalResultMainline.lean`
  - `pnp3/Magnification/FinalResultWeakRoutes.lean`
  - `pnp3/Tests/WeakRouteSurfaceTests.lean`

If a required reading file is absent on the current branch, record that fact in
the report and continue from the available in-repository context.

## Goal

Create exactly:

```text
seed_packs/asymptotic_isostrong_route_audit_D0/README.md
seed_packs/asymptotic_isostrong_route_audit_D0/WORKER_PROMPT_D0.md
seed_packs/asymptotic_isostrong_route_audit_D0/reports/.gitkeep
seed_packs/asymptotic_isostrong_route_audit_D0/failures/.gitkeep
```

## README requirements

The README must include:

1. Status

   OPEN — D0 audit only.

   No Lean code.
   No TMVerifier sessions.
   No `SourceTheorem`.
   No `ResearchGapWitness`.
   No endpoint.

2. Why this exists

   PR13 killed `FormulaCertificateProviderPartial`.
   Post-PR13 D0 found two possible existing consumers.
   Now we must audit their non-vacuity and hardwiring safety.

3. Audit targets

   - `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
   - `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
   - `AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym`
   - Their final endpoints with `AntiChecker`

4. Central questions

   A. Is `hInDag` trivially dischargeable in-repo?

   B. Is the route vacuous for `canonicalAsymptoticSpec`?

   C. Does a DAG-side truth-table hardwiring twin exist?

   D. Does a syntax/rewrite/normalization attack analogue exist?

   E. Is `PromiseYesSubcubeCertificateAt` nontrivial at canonical params?

   F. Which route, if any, should be selected as next formal target?

5. Allowed outcome

   One markdown report.

6. Possible verdicts

   - `GREEN_EXISTING_ROUTE_NONVACUOUS`
   - `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS`
   - `RED_ROUTE_VACUOUS_OR_HARDWIRED`
   - `INCONCLUSIVE_NEEDS_LEAN_PROBE`

7. Forbidden scope

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

## Allowed scope

Only the seed pack skeleton files.

## Commands

Run:

```bash
./scripts/check.sh
```

## Required output format

```text
Task: asymptotic_isostrong_route_audit_D0 skeleton
Commit before:
Commit after:
Changed files:
D0 only: yes/no
Commands run:
Scope violations:
```
