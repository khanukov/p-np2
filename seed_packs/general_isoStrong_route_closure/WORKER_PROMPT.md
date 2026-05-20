# Worker prompt — general iso-strong route closure

Branch: `main`.

Task type: **L1 route-level packaging** (named-theorem corollaries
of `isoStrong_conclusion_negative_general`).

## Goal

Land one new Lean test-local file
`pnp3/Tests/GeneralIsoStrongRouteClosure.lean` and register it in
`lakefile.lean`.

The file must provide four small named theorems, all kernel-checked,
all derivable from theorems already on `main` (no new proof
mathematics required):

1. `not_AsymptoticIsoStrongRoute_of_hInDag` — parameter-agnostic:
   ```
   (hAsym : AsymptoticFormulaTrackHypothesis)
   (hInDag : ∀ n β, InPpolyDAG
       (gapPartialMCSP_Language
         ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))) :
   ¬ AsymptoticIsoStrongRoute hAsym
   ```
   Proof: unfold `AsymptoticIsoStrongRoute hAsym` at the supplied
   `hInDag` and discharge against
   `GeneralIsoStrongNoGoProbe.isoStrong_conclusion_negative_general`.

2. `not_AsymptoticIsoStrongRoute_canonical` — canonical
   specialisation via
   `HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`
   (from L0 #1388).

3. `not_AsymptoticPromiseYesCertificateRoute_canonical` — corollary
   of (2) via the pointwise bridge
   `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
   (`pnp3/Magnification/FinalResultMainline.lean:400`).

4. `not_AsymptoticPromiseYesWeakRouteEventually_canonical` — corollary
   of (3) via the pointwise bridge
   `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
   (`pnp3/Magnification/FinalResultMainline.lean:348`).

Also update STATUS.md to record the named route closures.

## Constraints

- File-local to `pnp3/Tests/`; non-endpoint.
- Register in `lakefile.lean` (and register the previously-
  unregistered `Tests.HInDagTrivialityProbe` so the canonical
  specialisation builds).
- No endpoint, spec, JSONL, NoGoLog (operator approval pending),
  `known_guards`, or trust-root edits.
- No `axiom` / `opaque` / `sorry` / `admit` / `native_decide`.
- No new `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  or `P ≠ NP` claim.
- Reuse existing theorems verbatim; no re-proofs.

## Required reading

- `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`
  (`isoStrong_conclusion_negative_general`).
- `pnp3/Tests/HInDagTrivialityProbe.lean`
  (`hInDag_for_canonicalAsymptoticHAsym`).
- `pnp3/Magnification/FinalResultMainline.lean:218, 238, 265, 348, 400`
  (route defs + bridge theorems).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean:211`
  (`canonicalAsymptoticHAsym`).

## Commands

```sh
lake build Tests.GeneralIsoStrongRouteClosure
lake build PnP3 Pnp4
./scripts/check.sh
```

## Required output format

```
Task: general iso-strong route closure
Handle: <handle>
Commit before: <hash>
Commit after: <hash>
Outcome: ROUTE_CLOSURE_LANDED | STRUCTURED_FAILURE
Executive verdict: ROUTES_NAMED_AS_CLOSED | ...
Scope violations: none | <list>
```
