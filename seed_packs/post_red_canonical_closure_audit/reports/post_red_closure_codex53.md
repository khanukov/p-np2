# Task: post-RED canonical closure audit

Handle: codex53
Commit before: TBD
Commit after: TBD
Outcome: completed

## 1. Executive verdict

**ISO_RED_PROMISE_OVERCLAIM**

## 2. What is formally proved

The theorem that is explicitly kernel-proved is:

- `Pnp3.Tests.IsoStrongConclusionProbe.isoStrong_conclusion_negative_for_canonical`
- File: `pnp3/Tests/IsoStrongConclusionProbe.lean`

Statement summary: for every
`W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`,
`IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym) (globalWitness_to_hInDag W)` is false.

This is a direct negation of the canonical iso-strong route under the global witness contract.

## 3. What STATUS.md claims

Claim audit:

1. **iso-strong route closed**
   - Classification: **theorem-backed**
   - Reason: directly matches `isoStrong_conclusion_negative_for_canonical`.

2. **promise-YES weak route closed**
   - Classification: **overclaim**
   - Reason: no theorem in the required reading explicitly proves
     `¬ AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym`
     nor a canonical-global variant.

3. **promise-YES certificate route closed**
   - Classification: **overclaim**
   - Reason: no theorem in the required reading explicitly proves
     `¬ AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
     nor a canonical-global variant.

4. **canonical asymptotic track closed**
   - Classification: **plausible but not formal**
   - Reason: iso-strong leg is formally negative, and promise routes are upstream/convertible in the positive direction, but explicit negation theorems for promise routes are not present in the inspected files.

## 4. Promise route dependency audit

Inspected dependencies show:

- `AsymptoticPromiseYesWeakRouteEventually -> AsymptoticPromiseYesCertificateRoute`
  via theorem
  `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`.
- `AsymptoticPromiseYesCertificateRoute -> AsymptoticIsoStrongRoute`
  via theorem
  `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`.
- Promise routes feed final DAG endpoints through this conversion chain.

Therefore, **iso-strong negative does imply promise negative by contraposition**, but this implication is currently only derivable as a meta-proof composition and is not packaged as explicit named theorem(s) in the inspected surfaces.

Conclusion for this section:
- Direct theorem `isoStrong negative -> promise negative` is **not currently exposed** as a dedicated theorem.
- Promise-route closure needs either:
  - explicit companion theorem(s), or
  - STATUS wording that says promise closure is by logical consequence of existing conversion lemmas plus iso-strong negation.

## 5. Recommended correction

Recommended STATUS wording change (minimal and precise):

> The canonical iso-strong route is formally refuted by
> `isoStrong_conclusion_negative_for_canonical`.
> The canonical promise-YES weak/certificate routes are not yet stated as
> standalone negation theorems in this file set; their closure follows by
> contrapositive composition of existing route-conversion lemmas into
> iso-strong plus the iso-strong negation theorem.

Companion theorem targets (if preferred instead of wording-only patch):

- `promiseYesCertificate_conclusion_negative_for_canonical`:
  `∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
     ¬ AsymptoticPromiseYesCertificateRoute_global canonicalAsymptoticHAsym W`
  (or repository-preferred equivalent shape).
- `promiseYesWeak_conclusion_negative_for_canonical`:
  analogous explicit negation theorem for weak route.

## 6. Next action

**patch_status_wording**

---

Theorem-backed claims:
- iso-strong route closed.

Overclaims:
- promise-YES weak route closed (as standalone formal theorem claim).
- promise-YES certificate route closed (as standalone formal theorem claim).

Recommended next action:
- patch_status_wording

Scope violations:
- none
