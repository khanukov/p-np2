# general_isoStrong_route_closure

Seed pack for the route-closure packaging PR following L1 session 4
(`general_isoStrong_no_go_L1` chain, merged through `24d51510`).

## Why this pack exists

L1 session 4 landed `isoStrong_conclusion_negative_general` in
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`:

```lean
theorem isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
    ¬ IsoStrongFamilyEventually F hInDag
```

But this statement says nothing **directly** about the named route
props `AsymptoticIsoStrongRoute`, `AsymptoticPromiseYesCertificateRoute`,
`AsymptoticPromiseYesWeakRouteEventually`.  A future reader scanning
the route catalogue could see those route props and treat them as
surviving, since their refutation is presently available only as a
meta-argument rather than as a packaged named theorem.

This pack lands four small named theorems that explicitly close the
gap.

## Scope

- One new Lean test-local file: `pnp3/Tests/GeneralIsoStrongRouteClosure.lean`.
- One lakefile registration line for the new file (and one for the
  previously-unregistered `Tests.HInDagTrivialityProbe`).
- STATUS.md update recording the route closure.
- No endpoint, spec, JSONL, NoGoLog (operator approval pending),
  `known_guards`, or trust-root edits.
- No new `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  or `P ≠ NP` claim.
- No kernel-incomplete proof placeholders or escape hatches.

## What lands

In `pnp3/Tests/GeneralIsoStrongRouteClosure.lean`:

1. `not_AsymptoticIsoStrongRoute_of_hInDag` — parameter-agnostic
   helper: under any per-slice `InPpolyDAG` witness family for the
   slice-family induced by `hAsym`, `AsymptoticIsoStrongRoute hAsym`
   is empty.
2. `not_AsymptoticIsoStrongRoute_canonical` — canonical specialisation
   via `HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`.
3. `not_AsymptoticPromiseYesCertificateRoute_canonical` — direct
   corollary of (2) via the existing pointwise bridge
   `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`.
4. `not_AsymptoticPromiseYesWeakRouteEventually_canonical` — direct
   corollary of (3) via the existing pointwise bridge
   `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`.

All four have axiom dependencies `[propext, Classical.choice, Quot.sound]`.

## What does NOT change

- `isoStrong_conclusion_negative_general` and the L1 chain are
  re-used as-is; no proof code changes.
- The route-implication bridges in `pnp3/Magnification/FinalResultMainline.lean`
  are re-used as-is; no proof code changes.
- The L0 truth-table hardwiring witness
  `HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym` is
  re-used as-is; no proof code changes.

## Build verification (local, lean4 v4.22.0-rc2)

- `lake build Tests.GeneralIsoStrongRouteClosure` → success.
- `lake build PnP3 Pnp4` → success.
- `./scripts/check.sh` → exit 0, **"All checks passed"**, all 17
  steps green.
- `#print axioms` for all four landed theorems → `[propext,
  Classical.choice, Quot.sound]` only.

## Follow-ups (not in this pack)

- **NoGoLog entry** for the three closed routes — requires operator
  approval per repository governance.
- **Pivot to next route family** — the iso-strong / promise-YES
  certificate / promise-YES weak route closures collectively retire
  the iso-strong route class.  Future research must pivot to
  `SearchMCSPWeakLowerBound` (pnp4 frontier), restricted-model
  `gapPartialMCSP_not_in_AC0`, or genuinely new research-level
  mathematics.
