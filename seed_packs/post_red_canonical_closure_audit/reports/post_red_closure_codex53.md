# Task: post-RED canonical closure audit

Handle: codex53
Commit before: TBD
Commit after: TBD
Outcome: completed

## 1. Executive verdict

**ISO_RED_PROMISE_OVERCLAIM**

Iso-strong conclusion-side closure at canonical data is theorem-backed
by a single named, kernel-checked theorem.  The promise-YES weak and
promise-YES certificate route closures are derivable as pointwise
contrapositives of existing route-level implications, but are not
exposed as standalone Lean theorems in the inspected files; STATUS.md
prose treating all three routes as on equal "theorem-backed" footing
therefore reads as an overclaim under strict interpretation.
Recommended remediation is wording-level (see section 5).

## 2. What is formally proved

The theorem that is explicitly kernel-proved is:

- `Pnp3.Tests.IsoStrongConclusionProbe.isoStrong_conclusion_negative_for_canonical`
- File: `pnp3/Tests/IsoStrongConclusionProbe.lean`, line 368.

Statement (paraphrase):

```lean
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
```

This is a direct negation of the canonical iso-strong route under the
global witness contract, at the `globalWitness_to_hInDag W` projection
class of `hInDag`.

**Inhabitancy caveat.**  `GlobalAsymptoticDAGWitness
canonicalAsymptoticHAsym` is referenced only as a universal hypothesis
(`∀ W : ...`) in the inspected files; no explicit inhabitant is
constructed in the current codebase.  The `∀ W, ¬P(W)` theorem is
logically meaningful as-is, but its information content for downstream
closure narratives depends on an inhabitant being available at the
call site.  This is recorded as context, not as a verdict driver.

## 3. What STATUS.md claims

Claim audit:

1. **iso-strong route closed**
   - Classification: **theorem-backed**
   - Reason: directly matches `isoStrong_conclusion_negative_for_canonical`
     at `pnp3/Tests/IsoStrongConclusionProbe.lean:368`.

2. **promise-YES weak route closed**
   - Classification: **overclaim** (as standalone Lean theorem claim);
     **follows by existing theorem** (as pointwise contrapositive
     derivation).
   - Reason: no theorem in the required reading explicitly proves
     `¬ AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym`
     nor a canonical-global variant at body level.  Derivation via
     `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
     plus claim 3 below is available (see section 4).

3. **promise-YES certificate route closed**
   - Classification: **overclaim** (as standalone Lean theorem claim);
     **follows by existing theorem** (as pointwise contrapositive
     derivation).
   - Reason: no theorem in the required reading explicitly proves
     `¬ AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
     nor a canonical-global variant at body level.  Derivation via
     `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
     plus claim 1 is available (see section 4).

4. **canonical asymptotic track closed**
   - Classification: **plausible but not formal** (as a single
     theorem-level umbrella claim).
   - Reason: iso-strong leg is formally negative; promise routes are
     upstream/convertible in the positive direction and refutable in
     the negative direction by contrapositive of existing route-level
     implications, but explicit body-level negation theorems for
     promise routes are not present in the inspected files.

## 4. Promise route dependency audit

Inspected route-conversion theorems in
`pnp3/Magnification/FinalResultMainline.lean`:

- `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
  at line 348 — `weak → certificate`.
- `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
  at line 400 — `certificate → iso-strong`.
- Promise routes feed final DAG endpoints through this conversion
  chain (e.g.,
  `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`).

**Pointwise vs route-level implication.**  Both implication theorems
are stated at route level (Prop over `∀ hInDag, body hInDag`), but
their proofs open with `intro hInDag` and operate on the body at that
specific `hInDag`.  This means they are effectively **pointwise**: for
every `hInDag`, the certificate-body at `hInDag` implies the
iso-strong-body at `hInDag`, and similarly for weak → certificate.

Taking pointwise contrapositives at `hInDag = globalWitness_to_hInDag W`:

- `¬ iso_strong_body @ globalWitness_to_hInDag W` (this is exactly
  `isoStrong_conclusion_negative_for_canonical W` after unfolding) →
  `¬ certificate_body @ globalWitness_to_hInDag W`.
- `¬ certificate_body @ globalWitness_to_hInDag W` →
  `¬ weak_body @ globalWitness_to_hInDag W`.

So promise-YES negative results are mathematically present **at the
same W-projection** as the iso-strong negative theorem.

**However**, this is a meta-proof composition: the body-level
contrapositive of a route-level Prop implication does not appear in
Lean as a named theorem.  Producing it explicitly would require either
(a) a small adapter exposing the pointwise body implication, or (b) a
short corollary that reuses the existing implication proof structure
at one fixed `hInDag` and applies the iso-strong negation.

Conclusion for this section:

- Direct theorem `iso-strong negative → promise negative` is **not
  currently exposed** as a dedicated named theorem at body level.
- Promise-route closure is therefore **derivation-closed** but not
  **packaged-theorem-closed**.  The gap is presentational, not
  mathematical.

## 5. Recommended correction

Recommended STATUS wording change (minimal and precise):

> The canonical iso-strong route is formally refuted by
> `isoStrong_conclusion_negative_for_canonical`
> (`pnp3/Tests/IsoStrongConclusionProbe.lean:368`).  The canonical
> promise-YES weak and promise-YES certificate routes are not yet
> stated as standalone negation theorems in the probe file set; their
> body-level closure at `globalWitness_to_hInDag W` follows by
> pointwise contrapositive of the existing route-level implications
> `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
> (`pnp3/Magnification/FinalResultMainline.lean:348`) and
> `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
> (`pnp3/Magnification/FinalResultMainline.lean:400`) plus the
> iso-strong negation theorem.

Companion theorem targets (if preferred instead of wording-only
patch — recorded for completeness, not as a precondition for this
audit's recommended next action):

- `promiseYesCertificate_conclusion_negative_for_canonical`:
  `∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
     ¬ AsymptoticPromiseYesCertificateRoute_global canonicalAsymptoticHAsym W`
  (or repository-preferred equivalent body-level shape).  Expected
  proof: one-line via pointwise contrapositive of line 400 plus
  `isoStrong_conclusion_negative_for_canonical W`.
- `promiseYesWeak_conclusion_negative_for_canonical`:
  analogous explicit negation theorem for the weak route, derivable
  one-line from the certificate variant plus line 348's contrapositive.

## 6. Next action

**patch_status_wording**

Rationale: the gap is presentational (STATUS speaks of promise-route
"theorem-backed closure" where only derivation-closure is present).  A
wording patch citing the existing implication theorems with file:line
references is the smallest honest correction.  Companion theorems
remain optional; they would upgrade the attribution but are not
required to remove the overclaim.

---

Theorem-backed claims:
- iso-strong route closed (at the `globalWitness_to_hInDag W`
  projection class of `hInDag`).

Overclaims:
- promise-YES weak route closed (as standalone formal theorem claim).
- promise-YES certificate route closed (as standalone formal theorem
  claim).

Follows-by-existing-theorem claims:
- promise-YES weak route closure at `globalWitness_to_hInDag W` via
  pointwise contrapositive of
  `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`.
- promise-YES certificate route closure at `globalWitness_to_hInDag W`
  via pointwise contrapositive of
  `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`.

Recommended next action:
- patch_status_wording

Scope violations:
- none.  Markdown-only; no Lean source, spec, JSONL, NoGoLog,
  known_guards, or trust-root edits; no `ResearchGapWitness`,
  `SourceTheorem`, `gap_from`, endpoint, or `P ≠ NP` claim.
