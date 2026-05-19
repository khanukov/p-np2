# Worker prompt — post-RED canonical closure audit

Branch: `main` (base).  Markdown-only.

Task type: **D0 audit**.  Do not write Lean code unless follow-up
explicitly authorises a companion theorem.

## Goal

Produce exactly one report:

```text
seed_packs/post_red_canonical_closure_audit/reports/post_red_closure_<HANDLE>.md
```

Verify whether STATUS.md's claim that "the iso-strong route, the
promise-YES weak route, and the promise-YES certificate route at the
canonical spec are all inconsistent at the conclusion side under the
`GlobalAsymptoticDAGWitness` contract" is theorem-backed for each
of the three routes.

## Required reading

- `RESEARCH_CONSTITUTION.md`
- `STATUS.md` (the new note section about the canonical track being
  formally closed)
- `pnp3/Tests/IsoStrongConclusionProbe.lean`
  (`isoStrong_conclusion_negative_for_canonical` at line 368)
- `pnp3/Tests/GlobalHInDagContractProbe.lean`
  (the `GlobalAsymptoticDAGWitness` contract)
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean`
  (`IsoStrongFamilyEventually` at lines 1078–1104)
- `pnp3/Magnification/FinalResultMainline.lean`
  (`AsymptoticIsoStrongRoute` at line 218,
   `AsymptoticPromiseYesCertificateRoute` at line 238,
   `AsymptoticPromiseYesWeakRouteEventually` at line 265,
   `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
   at line 348,
   `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
   at line 400)
- `pnp3/Tests/CanonicalIntegrationTests.lean`

## Required report sections

The report must include:

1. **Executive verdict** — exactly one of:
   - `ISO_ONLY_RED_STATUS_OK`
   - `ISO_RED_PROMISE_OVERCLAIM`
   - `ISO_AND_PROMISE_RED_FORMALLY_SUPPORTED`
   - `NEEDS_COMPANION_PROMISE_THEOREM`

2. **What is formally proved** — quote/summarize
   `isoStrong_conclusion_negative_for_canonical` with exact file +
   line.  Also flag whether `GlobalAsymptoticDAGWitness
   canonicalAsymptoticHAsym` has an inhabitant in Lean (it does not
   in the current codebase; the structure is used only as a universal
   ∀-hypothesis).

3. **What STATUS.md claims** — list each claim:
   - iso-strong route closed
   - promise-YES weak route closed
   - promise-YES certificate route closed
   - canonical asymptotic track closed (the umbrella claim)

   Classify each as:
   - theorem-backed (direct Lean theorem of the same shape)
   - follows by existing theorem (one or two `apply` calls / a clear
     contrapositive of an existing theorem)
   - plausible but not formal (true mathematically but no Lean proof
     path identified)
   - overclaim (not derivable without additional non-trivial work)

4. **Promise route dependency audit** — inspect:
   - `AsymptoticPromiseYesCertificateRoute`
   - `AsymptoticPromiseYesWeakRouteEventually`
   - `PromiseYesSubcubeCertificateAt`
   - final endpoints using promise routes (e.g.,
     `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`)

   Answer the key question: does
   `isoStrong_conclusion_negative_for_canonical` directly imply
   negation of the promise-YES routes' bodies at the same
   `globalWitness_to_hInDag W`, or does each promise route need a
   separately stated negation theorem?

   Examine the direction of the existing implication theorems:
   - `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually : weak → certificate`
   - `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute : certificate → iso-strong`

   Check whether these are POINTWISE implications (operating per
   hInDag) or ROUTE-LEVEL implications (operating on the universally-
   quantified Prop).  This determines whether contrapositive can be
   used at the body level.

5. **Recommended correction** —
   - If `ISO_ONLY_RED_STATUS_OK`: no correction needed.
   - If `ISO_RED_PROMISE_OVERCLAIM`: propose exact STATUS.md wording
     change to limit the closure claim to iso-strong only.
   - If `NEEDS_COMPANION_PROMISE_THEOREM`: state the exact target
     theorem signatures for promise-YES certificate and promise-YES
     weak refutations.

6. **Next action** — exactly one of:
   - `merge_status_as_is`
   - `patch_status_wording`
   - `open_promise_companion_L0`
   - `close_canonical_track_fully`

## Forbidden scope

No Lean code.  No source edits.  No JSONL / spec / `known_guards` /
NoGoLog / trust-root edits.  No `ResearchGapWitness`, `SourceTheorem`,
`gap_from`, endpoint, `P ≠ NP` claim.

## Commands

```sh
./scripts/check.sh
```

## Required output format

```
Task: post-RED canonical closure audit
Handle: <handle>
Commit before: <hash>
Commit after: <hash>
Outcome: REPORT_LANDED | STRUCTURED_FAILURE
Executive verdict: <one of the four>
Theorem-backed claims: <list>
Overclaims: <list, or "none">
Recommended next action: <one of the four>
Scope violations: <none | list>
```
