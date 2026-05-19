# Post-RED canonical asymptotic closure audit

## 1. Executive verdict

**NEEDS_COMPANION_PROMISE_THEOREM**

Reason: the repository has a formal RED theorem for the iso-strong conclusion route at canonical data, but STATUS currently states that promise-YES weak and certificate routes are also conclusion-side inconsistent without a dedicated theorem proving those promise routes are impossible under the same canonical/global contract.

## 2. What is formally proved

The following theorem is present and kernel-checked:

- `pnp3/Tests/IsoStrongConclusionProbe.lean`
- theorem `isoStrong_conclusion_negative_for_canonical`

Statement (paraphrase): for every `W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`,
`IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym) (globalWitness_to_hInDag W)` is false.

This is an explicit conclusion-side negation theorem for the iso-strong family under canonical asymptotic data and the global witness contract.

## 3. What STATUS.md claims

Claims audited:

1. **iso-strong route closed**
   - Classification: **theorem-backed**.
   - Basis: direct theorem `isoStrong_conclusion_negative_for_canonical` exists.

2. **promise-YES weak route closed**
   - Classification: **plausible but not formal** (current tree evidence).
   - Basis: I did not find a theorem directly negating
     `AsymptoticPromiseYesWeakRouteEventually_global canonicalAsymptoticHAsym`
     nor a theorem deriving that negation from
     `isoStrong_conclusion_negative_for_canonical`.

3. **promise-YES certificate route closed**
   - Classification: **plausible but not formal** (current tree evidence).
   - Basis: I did not find a theorem directly negating
     `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
     nor an explicit theorem reducing this route to contradiction via the canonical/global assumptions.

4. **canonical asymptotic track closed**
   - Classification: **overclaim** in strict theorem-backed wording.
   - Basis: iso-strong closure is formal; promise-route closure appears asserted by expected compositional analogy, but lacks explicit companion negative theorem(s).

## 4. Promise route dependency audit

Inspected definitions and route composition:

- `AsymptoticPromiseYesWeakRouteEventually` (mainline source theorem shape).
- `AsymptoticPromiseYesCertificateRoute` (witness-indexed certificate route).
- `PromiseYesSubcubeCertificateAt` (certificate object used in conversion).
- Final endpoints:
  - `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute*`
  - `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute*`

Dependency direction in code is:

1. `AsymptoticPromiseYesWeakRouteEventually` ⇒
   `AsymptoticPromiseYesCertificateRoute` via
   `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`.
2. `AsymptoticPromiseYesCertificateRoute` ⇒
   `AsymptoticIsoStrongRoute` via
   `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`.
3. Final certificate endpoints route through the iso-strong endpoint.

Therefore, **isoStrong negative does not automatically negate promise routes unless a theorem explicitly instantiates and composes these implications under the same hypothesis domain** (here: canonical track with `GlobalAsymptoticDAGWitness`/`globalWitness_to_hInDag`).

In short:

- Logical shape suggests promise negatives should be derivable.
- But a dedicated proved theorem is still needed to upgrade STATUS wording from “expected by composition” to “formally proved”.

## 5. Recommended correction

If keeping current theorem set unchanged, update STATUS wording to:

> The canonical iso-strong conclusion route is formally refuted by
> `isoStrong_conclusion_negative_for_canonical`. The analogous
> promise-YES weak/certificate conclusion-side closure is expected by
> existing route implications and is pending an explicit companion theorem.

If preferring full formal support now, target companion theorem(s):

1. `promiseYesCertificate_conclusion_negative_for_canonical`:
   negates canonical `AsymptoticPromiseYesCertificateRoute` under global witness contract by composition to iso-strong then contradiction.
2. (Optional direct) `promiseYesWeak_conclusion_negative_for_canonical`:
   negates canonical `AsymptoticPromiseYesWeakRouteEventually_global` by first converting weak→certificate and reusing (1).

## 6. Next action

**open_promise_companion_L0**

Rationale: this is the minimal action that converts the current plausible closure narrative for promise routes into theorem-backed closure claims aligned with strict audit language.
