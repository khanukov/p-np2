# General iso-strong route closure

Task: general iso-strong route closure
Handle: opus47
Branch: main

## 1. Executive verdict

**ROUTES_NAMED_AS_CLOSED**

Four named theorems landed in
`pnp3/Tests/GeneralIsoStrongRouteClosure.lean`, all kernel-checked
with standard kernel axioms only.  The iso-strong, promise-YES
certificate, and promise-YES weak route props are now explicitly
refuted at the canonical asymptotic instantiation.

## 2. What landed

In `pnp3/Tests/GeneralIsoStrongRouteClosure.lean`:

1. `not_AsymptoticIsoStrongRoute_of_hInDag` — parameter-agnostic
   helper.  Under any per-slice `InPpolyDAG` witness family for the
   slice-family induced by `hAsym`, `AsymptoticIsoStrongRoute hAsym`
   is empty.
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

2. `not_AsymptoticIsoStrongRoute_canonical` — canonical specialisation
   using `HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`
   from L0 #1388.
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

3. `not_AsymptoticPromiseYesCertificateRoute_canonical` — corollary
   of (2) via the pointwise bridge
   `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
   (`pnp3/Magnification/FinalResultMainline.lean:400`).
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

4. `not_AsymptoticPromiseYesWeakRouteEventually_canonical` — corollary
   of (3) via the pointwise bridge
   `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
   (`pnp3/Magnification/FinalResultMainline.lean:348`).
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

Module registered in `lakefile.lean` as
`Glob.one \`Tests.GeneralIsoStrongRouteClosure`.  Also registered
the previously-unregistered `Tests.HInDagTrivialityProbe` (existed
since L0 #1388 but was not in the `PnP3` lib glob), so the
canonical specialisation theorem (2) can build via the lib.

## 3. Why this matters

Before this PR, the strategic consequence of
`isoStrong_conclusion_negative_general` (merged in `24d51510`) was
present only as a meta-argument: a future reader scanning the
catalogue of route props in `pnp3/Magnification/FinalResultMainline.lean`
could see `AsymptoticIsoStrongRoute`,
`AsymptoticPromiseYesCertificateRoute`, and
`AsymptoticPromiseYesWeakRouteEventually` and mistakenly treat them
as surviving routes — since their refutation required composing
`isoStrong_conclusion_negative_general` with route-implication
bridges by hand.

After this PR the route closures are **named theorems** that any
future reader can find by `grep`.  This makes the iso-strong /
promise-YES weak / promise-YES certificate route class formally
retired at the canonical asymptotic instantiation, with no
ambiguity about which routes are still open.

## 4. STATUS.md update

The L1 chain summary section in `STATUS.md` is updated to record
the four route closures and point at the new file.  No claim about
`P ≠ NP` or `NP ⊄ P/poly` is added.

## 5. Build verification (local, lean4 v4.22.0-rc2)

- `lake build Tests.GeneralIsoStrongRouteClosure` → success.
- `lake build PnP3 Pnp4` → success.
- `./scripts/check.sh` → exit 0, **"All checks passed"**, all 17
  steps green.
- `#print axioms` for all four landed theorems → standard kernel
  axioms only.

## 6. Scope violations

none.  One new test-local Lean file, two `lakefile.lean` glob
entries, one STATUS.md prose paragraph, and one seed-pack scaffold.
No endpoint, spec, JSONL, NoGoLog, `known_guards`, or trust-root
edits.  No `ResearchGapWitness`, `SourceTheorem`, `gap_from`,
endpoint, or `P ≠ NP` claim.

## 7. Recommended next action

**close_isoStrong_route_pattern_refuted** (this PR closes that
action item).

Optional follow-ups (not in this pack):

- NoGoLog entry for the three closed routes — pending operator
  approval per repository governance.
- Pivot to next route family: pnp4 frontier
  `SearchMCSPWeakLowerBound` / `VerifiedNPDAGLowerBoundSource`,
  restricted-model `gapPartialMCSP_not_in_AC0`, or new research-
  level mathematics.
