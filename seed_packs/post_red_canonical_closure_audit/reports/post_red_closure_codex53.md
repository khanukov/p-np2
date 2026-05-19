# Task: post-RED canonical closure audit

Handle: codex53
Commit before: pending
Commit after: pending
Outcome: completed
Executive verdict: ISO_AND_PROMISE_RED_FORMALLY_SUPPORTED
Theorem-backed claims: iso-strong route closed; promise-YES weak route closed (via existing bridge theorem chain); promise-YES certificate route closed (by reduction to iso-strong)
Overclaims: none found in the scoped claims below
Recommended next action: merge_status_as_is
Scope violations: none

---

## 1. Executive verdict

**ISO_AND_PROMISE_RED_FORMALLY_SUPPORTED**

Reason: the canonical iso-strong route is directly refuted by a named theorem, and both promise routes reduce to iso-strong through existing in-repo theorem bridges.

## 2. What is formally proved

The central RED theorem is:

- `pnp3/Tests/IsoStrongConclusionProbe.lean`
- theorem: `isoStrong_conclusion_negative_for_canonical`

Statement (summarized):

For every `W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`,
`IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym) (globalWitness_to_hInDag W)` is false.

This is a direct contradiction result for the canonical iso-strong conclusion side.

## 3. What STATUS.md claims

Claims audited:

1. **iso-strong route closed**  
   Classification: **theorem-backed**.  
   Basis: explicit theorem `isoStrong_conclusion_negative_for_canonical`.

2. **promise-YES weak route closed**  
   Classification: **follows by existing theorem**.  
   Basis: `AsymptoticPromiseYesWeakRouteEventually` is transformed to the certificate route by
   `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`; the certificate route then implies iso-strong (and thereby contradiction under the canonical/global witness setting).

3. **promise-YES certificate route closed**  
   Classification: **follows by existing theorem**.  
   Basis: the certificate route is funneled into the iso-strong route in `FinalResultMainline` (`NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute` uses `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`). Combined with canonical iso-strong negation, this closes the canonical certificate path.

4. **canonical asymptotic track closed**  
   Classification: **follows by existing theorem** (for the canonical track and scoped route family).  
   Basis: all three route surfaces called out in STATUS reduce to the refuted iso-strong conclusion under canonical/global-witness contract.

## 4. Promise route dependency audit

Inspected objects:

- `AsymptoticPromiseYesCertificateRoute`
- `AsymptoticPromiseYesWeakRouteEventually`
- `PromiseYesSubcubeCertificateAt`
- final DAG/P≠NP endpoints using promise routes

Dependency conclusions:

- **Does isoStrong negative directly imply promise negative?**  
  Not as a standalone syntactic implication theorem in one line, but **effectively yes through existing route-reduction theorems** in `FinalResultMainline`.

- **Does promise need separate theorem?**  
  For closure status in this canonical audit, **no additional companion theorem is required**. Existing theorem chain is sufficient:
  - weak route ⇒ certificate route (`asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`)
  - certificate route ⇒ iso-strong route (used by `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute`)
  - canonical iso-strong is impossible (`isoStrong_conclusion_negative_for_canonical`)

## 5. Recommended correction

No wording patch is required for the four scoped STATUS claims.

Optional precision improvement (non-mandatory): in STATUS prose, keep the qualifier “at canonical spec / under GlobalAsymptoticDAGWitness contract” adjacent to all three route-closure statements to make the scope visually explicit.

## 6. Next action

**merge_status_as_is**

Rationale: the audited claims are theorem-backed directly or by clean theorem reduction chains already present in the repository.
