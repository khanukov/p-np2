# post-RED canonical closure audit

## 1. Status

**D0 audit only.**  Markdown-only.

No Lean code unless explicitly authorised in the follow-up.  No source
edits.  No `SourceTheorem`, `ResearchGapWitness`, `gap_from`, endpoint,
or `P ≠ NP` claim.

## 2. Why this exists

After L1 session 4 (PR #1433 squash `3a3681a`) landed
`isoStrong_conclusion_negative_for_canonical`, STATUS.md (PR #1435
squash `e1b4b08`) was updated to claim the canonical asymptotic track
is formally closed at conclusion level, including all three routes
(iso-strong, promise-YES weak, promise-YES certificate).

This audit verifies whether each of those three claims is
**theorem-backed** in Lean, or whether the promise-YES claims are
follows-by-existing-theorem consequences that require companion
theorems for honest Lean attestation.

## 3. Central question

For each of the three claimed-closed routes:

1. `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym` — closed?
2. `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym` — closed?
3. `AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym` — closed?

Where "closed" means: under the `GlobalAsymptoticDAGWitness` contract,
the conclusion side is provably refutable via a Lean theorem (direct
or one-line corollary).

## 4. Possible verdicts

- **`ISO_ONLY_RED_STATUS_OK`** — STATUS already limits the closure
  claim to iso-strong; no overclaim.
- **`ISO_RED_PROMISE_OVERCLAIM`** — STATUS includes promise-YES routes
  in the closure claim but no Lean theorem (direct or trivial
  corollary) backs that.
- **`ISO_AND_PROMISE_RED_FORMALLY_SUPPORTED`** — promise-YES routes are
  backed by a Lean theorem or follow trivially (zero-step or single
  `apply` corollary) from existing theorems.
- **`NEEDS_COMPANION_PROMISE_THEOREM`** — promise-YES routes' closure
  claim is mathematically derivable but requires explicit 2–3 line
  companion theorems in Lean to be fully theorem-backed.

## 5. Required sections in the report

1. Executive verdict.
2. What is formally proved (quote theorem signature, file, line).
3. What STATUS.md claims (enumerate + classify each claim).
4. Promise route dependency audit (does iso-strong RED imply
   promise-YES RED via existing implication theorems?).
5. Recommended correction (wording or companion theorem signatures).
6. Next action.

## 6. Audit targets (read-only)

- `RESEARCH_CONSTITUTION.md`.
- `STATUS.md` (current claims).
- `pnp3/Tests/IsoStrongConclusionProbe.lean`
  (`isoStrong_conclusion_negative_for_canonical`).
- `pnp3/Tests/GlobalHInDagContractProbe.lean` (contract structure).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean`
  (`IsoStrongFamilyEventually`).
- `pnp3/Magnification/FinalResultMainline.lean:218–460` (route
  definitions + inter-route implications).
- `pnp3/Tests/CanonicalIntegrationTests.lean`.

## 7. Forbidden scope

- No Lean code unless explicitly authorised as a follow-up.
- No source edits.
- No JSONL / spec / `known_guards` / NoGoLog / trust-root edits.
- No `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  `P ≠ NP` claim.

## 8. Allowed scope

- ONE markdown report at
  `seed_packs/post_red_canonical_closure_audit/reports/post_red_closure_<HANDLE>.md`.
- Optional failure notes under `failures/`.
