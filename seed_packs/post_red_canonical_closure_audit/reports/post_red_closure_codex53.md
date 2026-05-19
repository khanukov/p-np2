# post-RED canonical asymptotic closure audit (`codex53`)

## 1. Executive verdict

**NEEDS_COMPANION_PROMISE_THEOREM**

Reason: `isoStrong_conclusion_negative_for_canonical` is formally proved and closes the iso-strong route. The promise-YES weak/certificate closures appear to follow *conceptually* via route-conversion lemmas, but the closure claim in `STATUS.md` is presented as if fully direct theorem-backed at conclusion side; this should be tightened unless an explicit companion theorem is added for promise-route negation.

## 2. What is formally proved

The following theorem is present and fully formalized:

- File: `pnp3/Tests/IsoStrongConclusionProbe.lean`
- Theorem: `isoStrong_conclusion_negative_for_canonical`
- Statement shape:
  - `∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,`
  - `¬ IsoStrongFamilyEventually (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym) (globalWitness_to_hInDag W)`

This is a direct canonical conclusion-side negative result for the iso-strong route under the global witness contract.

## 3. What STATUS.md claims

Claims and classification:

1. **iso-strong route closed**  
   Classification: **theorem-backed**.  
   Basis: `isoStrong_conclusion_negative_for_canonical` in `pnp3/Tests/IsoStrongConclusionProbe.lean`.

2. **promise-YES weak route closed**  
   Classification: **follows by existing theorem** (indirectly), but not stated in STATUS via a dedicated named companion negative theorem.  
   Basis chain: `AsymptoticPromiseYesWeakRouteEventually -> AsymptoticPromiseYesCertificateRoute -> AsymptoticIsoStrongRoute` in `pnp3/Magnification/FinalResultMainline.lean`; combined with iso-strong negative should yield contradiction under same canonical/global contract context.

3. **promise-YES certificate route closed**  
   Classification: **follows by existing theorem** (indirectly), via `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute` plus iso-strong negative.

4. **canonical asymptotic track closed**  
   Classification: **plausible but not formal** as a single direct theorem phrase at STATUS granularity, unless one accepts the route-conversion chain as sufficient closure evidence for each named route.

## 4. Promise route dependency audit

Inspected definitions and route-conversion surfaces:

- `AsymptoticPromiseYesCertificateRoute` (`pnp3/Magnification/FinalResultMainline.lean`): theorem-level certificate route schema.
- `AsymptoticPromiseYesWeakRouteEventually` (`pnp3/Magnification/FinalResultMainline.lean`): eventual weak-route schema.
- `PromiseYesSubcubeCertificateAt` usage:
  - constructor/transport in `promiseYesSubcubeCertificateAt_of_eventualPromiseYesWeakRoute`
  - conversion theorem `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
- final endpoints using promise routes (e.g., canonical integration test wrappers in `pnp3/Tests/CanonicalIntegrationTests.lean` and final mainline endpoints that accept promise-route hypotheses).

Conclusion:

- **Iso-negative does not directly mention promise-route hypotheses.**
- Promise-route closure currently depends on **bridge lemmas**:
  1. weak -> certificate, and
  2. certificate -> iso-strong,
  then apply iso-strong negative.
- Therefore promise-route negative is presently **derived/indirect**, not a standalone explicit companion theorem in the probe file.

## 5. Recommended correction

Since STATUS prose is strong, recommended wording adjustment (minimal):

> "The canonical iso-strong route is formally refuted by theorem
> `isoStrong_conclusion_negative_for_canonical`. The promise-YES weak and
> certificate routes reduce to iso-strong through existing conversion lemmas,
> so they are closed by derivation; a dedicated companion theorem for direct
> promise-route negation remains optional."

Companion theorem target (if desired for explicitness):

- `promiseYes_certificate_conclusion_negative_for_canonical`:
  `∀ W, ¬ AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym` under the matching global-contract instantiation context.
- optionally a weak-route variant via the weak->certificate conversion.

## 6. Next action

**open_promise_companion_L0**

Rationale: this removes ambiguity in STATUS classification by adding explicit theorem names for promise-route negation, making closure attribution theorem-direct rather than conversion-derived.
