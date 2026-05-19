# post-RED canonical closure audit — opus47

Date: 2026-05-19.
Commit base: `e1b4b08` (STATUS.md update after L1 session 4).

## 1. Executive verdict

**`NEEDS_COMPANION_PROMISE_THEOREM`**.

The iso-strong route is theorem-backed for the W-projection class
of hInDag.  The promise-YES weak and promise-YES certificate routes
are mathematically derivable via contrapositive of existing
route-level implications, but are **not separately stated as Lean
theorems**.  STATUS.md's claim that all three routes are formally
closed is **overclaim by strict interpretation** of "theorem-backed",
**accurate by relaxed interpretation** of "follows from existing
theorems via short corollary".

There is also a secondary structural concern (recorded but not the
primary verdict): the iso-strong theorem itself is stated as
`∀ W, ¬P(W-projection)`, which is informative only when at least
one `W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym` is
constructible.  No such inhabitant exists in the current Lean
codebase — the structure is used only as a universal hypothesis.

Two small (≤ 30 LOC) companion theorems would convert the current
"follows from existing theorem" status into proper theorem-backed
attestation:

```lean
theorem promiseYesCertificate_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ AsymptoticPromiseYesCertificateRouteAt
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
  -- one-line proof via contrapositive of asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute
  -- + isoStrong_conclusion_negative_for_canonical

theorem promiseYesWeakRoute_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ AsymptoticPromiseYesWeakRouteEventuallyAt
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
  -- one-line proof via contrapositive of
  -- asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually
  -- + promiseYesCertificate_conclusion_negative_for_canonical
```

(The exact predicate names `…RouteAt` need to be extracted as the
pointwise per-hInDag body forms; the existing route Props are
universal-quantified versions of these bodies.)

## 2. What is formally proved

The single Lean theorem in `pnp3/Tests/IsoStrongConclusionProbe.lean`
at line 368:

```lean
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
```

**This theorem is kernel-checked.**  Its proof composes:

- L0 slack extraction (`canonical_isoStrong_implies_eventual_strict_slack`);
- L0 contract projection (`globalWitness_to_hInDag`);
- L1 session 1 pigeonhole core (`exists_trace_not_size1_of_card_lt`);
- L1 session 2 encoding bridge (`diagonalPartialTable`,
  `diagonal_z_valid`, `diagonal_z_agrees_on_D`);
- L1 session 3 not-YES bridge (`diagonal_z_not_yes_of_label_not_trace`,
  `exists_valid_agreeing_not_yes_under_slack`);
- L1 session 4 final assembly
  (`correctOnPromiseSlice_of_InPpolyDAG_family`,
   `slack_for_D_of_isoStrong_slack`).

**Important caveat about inhabitancy.**
`GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym` is not
explicitly inhabited in the current Lean codebase.  Searches via
`grep -rn` confirm the structure is referenced only as a universal
hypothesis (`∀ W : ...`) in the negative theorem and in the
contract definition file.  Mathematically, the type IS inhabited
(the canonical asymptotic language is in P via `decideAsymptotic`,
so a polynomial-size DAG family exists), but the multi-session
TM-verifier construction needed to formally inhabit it has not
landed.

Thus: the theorem is correct (the universal is logically meaningful
and constructively proven), but its information content for closure
purposes depends on whether a W can be supplied at the call site.
The current Lean state cannot produce such a W constructively.

The proof of the theorem **itself does not depend on W's existence**
— it operates as `∀ W, ¬P(W)` over the type as-is.  The proof
structure uses only `InPpolyDAG` fields of `(globalWitness_to_hInDag W
n β)`, which are accessible from any `W`.  The proof generalises
trivially to `∀ hInDag : (∀ n β, InPpolyDAG ...), ¬IsoStrong ...`,
but the current statement is artificially restricted to W-projections.

## 3. What STATUS.md claims

The relevant note in STATUS.md (after PR #1435) contains these claims:

| # | Claim | Classification |
|---|-------|----------------|
| 1 | The iso-strong route at canonical is inconsistent at conclusion side | **theorem-backed** for W-projection class; **not theorem-backed** for arbitrary hInDag (current statement form does not cover the hardwired-from-#1388 hInDag class) |
| 2 | The promise-YES weak route at canonical is inconsistent at conclusion side | **follows by existing theorem** via contrapositive of `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually` + claim (3) |
| 3 | The promise-YES certificate route at canonical is inconsistent at conclusion side | **follows by existing theorem** via contrapositive of `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute` + claim (1) |
| 4 | The canonical asymptotic track is formally closed (umbrella claim) | **partial** — closed for iso-strong at W-projection class; promise routes follow via short corollary; the route Prop itself (`∀ hInDag, ...`) is not directly refuted at all hInDag in the current statement |

The umbrella claim "canonical asymptotic track formally closed" is
the strongest statement and the most at risk of overclaim.  Reading
the STATUS.md text literally, it says "all three routes are
**inconsistent at the conclusion side** under the `GlobalAsymptoticDAGWitness`
contract" — this is correctly qualified by "under the contract"
(i.e., at the W-projection class of hInDag, not at all hInDag).

The promise-YES claims, however, are not separately Lean-attested.

## 4. Promise route dependency audit

The two relevant implication theorems are in
`pnp3/Magnification/FinalResultMainline.lean`:

```lean
-- line 348:
theorem asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hRoute : AsymptoticPromiseYesWeakRouteEventually hAsym) :
    AsymptoticPromiseYesCertificateRoute hAsym

-- line 400:
theorem asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hRoute : AsymptoticPromiseYesCertificateRoute hAsym) :
    AsymptoticIsoStrongRoute hAsym := by
  intro hInDag
  rcases hRoute hInDag with ⟨β0, hβ0, nCert, hCert⟩
  ...
```

Both theorems operate at the **route level** (`∀ hInDag, body`).
But examining the proof structure: each begins with `intro hInDag`,
extracts the existential from `hRoute hInDag` at that specific
hInDag, then constructs the target body at the same hInDag.  This
means the implications are effectively **pointwise**:

> For every `hInDag`, the certificate body at `hInDag` implies the
> iso-strong body at `hInDag`.  Similarly weak → certificate at the
> same `hInDag`.

Taking contrapositives at the pointwise level:

- ¬iso_strong_body(hInDag) → ¬certificate_body(hInDag)
- ¬certificate_body(hInDag) → ¬weak_body(hInDag)

For `hInDag = globalWitness_to_hInDag W`, our theorem provides
¬iso_strong_body(W-projection).  By the two contrapositives in
sequence:

- ¬certificate_body(W-projection) follows.
- ¬weak_body(W-projection) follows.

So STATUS.md's promise-YES claims are **mathematically derivable**
via pointwise contrapositive of the existing route-level
implications.

**However**, taking the contrapositive of a route-level Prop
implication does NOT automatically yield the body-level
contrapositive in Lean — extracting the pointwise structure
requires either:

(a) An auxiliary lemma stating the pointwise body implication
    explicitly, or
(b) Manually re-running the proof of the route-level implication at
    a specific hInDag (which is what the companion theorems would do).

The companion theorems in section 1's recommended correction would
be ≤ 30 LOC each and would make the promise-YES claims **directly
theorem-backed** rather than "follows by short corollary".

## 5. Recommended correction

Two parts.

### Part A: optional STATUS.md wording patch

STATUS.md's current text:

> "The iso-strong route, the promise-YES weak route, and the
> promise-YES certificate route at the canonical spec are all
> inconsistent at the conclusion side under the (now Lean-witnessed)
> `GlobalAsymptoticDAGWitness` contract."

This is accurate IF the reader accepts that "inconsistent at the
conclusion side" includes consequences derivable via contrapositive
of existing route-level implications.

For maximum precision, the wording could be patched to:

> "The iso-strong route at the canonical spec is inconsistent at
> conclusion side via `isoStrong_conclusion_negative_for_canonical`
> (`pnp3/Tests/IsoStrongConclusionProbe.lean:368`).  The promise-YES
> weak route and the promise-YES certificate route are inconsistent
> at the same `GlobalAsymptoticDAGWitness` projection via the
> contrapositive of the existing route-level implications
> `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
> and `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
> (companion theorems pending in
> `seed_packs/post_red_canonical_closure_audit`)."

### Part B: companion theorems (the actual recommended action)

Two ≤ 30 LOC theorems extending
`pnp3/Tests/IsoStrongConclusionProbe.lean`:

```lean
theorem promiseYesCertificate_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ (∃ ε β0 : Rat, 0 < ε ∧ 0 < β0 ∧
          ∀ β : Rat, 0 < β → β < β0 →
            ∃ nCert : Rat → Nat, ...
            -- the body of AsymptoticPromiseYesCertificateRoute
            --   at hInDag = globalWitness_to_hInDag W) := by
  intro W hCert
  -- Convert hCert to an iso-strong witness at globalWitness_to_hInDag W
  -- using the pointwise version of
  -- asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute.
  -- Contradiction with isoStrong_conclusion_negative_for_canonical W.
  ...
```

A simpler formulation would package the body refutation directly:

```lean
theorem promiseYesCertificate_body_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ asymptoticPromiseYesCertificateBody
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
```

Either form would require:
1. A small adapter from the body shape to the form usable in the
   contrapositive (probably implicit in
   `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`'s
   proof internals).
2. One `apply isoStrong_conclusion_negative_for_canonical W`.

Estimated LOC: 15–30 per companion theorem.  Plus a small adapter
helper of similar size if needed.

The author of the L0 / L1 chain (codex via parallel dispatch) can
write these companion theorems in a single session.

## 6. Next action

**`open_promise_companion_L0`**.

Rationale: the recommended correction is "land 2 companion theorems
≤ 30 LOC each".  This is a small, well-scoped L0 task:

- Land `promiseYesCertificate_body_negative_for_canonical` in
  `pnp3/Tests/IsoStrongConclusionProbe.lean`.
- Land `promiseYesWeak_body_negative_for_canonical` in the same
  file.
- Each is a short corollary of
  `isoStrong_conclusion_negative_for_canonical` via the pointwise
  contrapositive of the existing route-level implications.

After landing, STATUS.md can be updated (markdown-only PR) to cite
all three companion theorems as direct backings of the umbrella
"canonical asymptotic track formally closed" claim.

Alternative (less invasive): `patch_status_wording` only —
explicitly state that promise-YES routes follow by contrapositive
of existing route implications, without landing companion theorems.
This is honest but leaves the promise-YES backing as "derivable
short corollary" rather than direct theorem.

I recommend `open_promise_companion_L0` because:
1. The companion theorems are very small (15–30 LOC each).
2. Direct theorem-backing is more rigorous than "follows by
   contrapositive of route-level theorem".
3. It preserves the audit chain's high standard of formal
   attestation set by the prior 11 stages.

A separate `merge_status_as_is` is NOT recommended — the strict
reading of "theorem-backed" leaves promise-YES claims under-attested.

## 7. Audit chain consistency notes

The full 11-stage chain (PR 13 + 6 D0/L0 + 4 L1 sessions) is
internally consistent and the artifacts are in main.  This audit's
findings do not invalidate any prior session — they only suggest a
small follow-up (~30–60 LOC across two companion theorems) to
strengthen the STATUS.md attestation.

The fundamental structural finding — that the canonical asymptotic
track is mathematically inconsistent at conclusion side under the
GlobalAsymptoticDAGWitness contract — is preserved.

## 8. Scope statement

This report introduces no Lean source, no spec, JSONL, NoGoLog,
known_guards, or trust-root edits.  No `ResearchGapWitness`,
`SourceTheorem`, `gap_from`, endpoint, or `P ≠ NP` claim.  Only this
markdown report under the seed pack's `reports/` directory was added.

## 9. Commands run

```sh
git rev-parse HEAD
git log --oneline -10
grep -n "^theorem isoStrong_conclusion_negative_for_canonical\|^theorem asymptotic.*Route_of_asymptotic.*Route\|^def AsymptoticPromiseYes\|^def AsymptoticIsoStrong" pnp3/Tests/IsoStrongConclusionProbe.lean pnp3/Magnification/FinalResultMainline.lean
grep -rn "GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym\b" pnp3
grep -rn "^def.*GlobalAsymptoticDAGWitness\|^theorem.*GlobalAsymptoticDAGWitness\|^example.*GlobalAsymptoticDAGWitness\|canonicalGlobalWitness\|canonical.*WitnessInhabit" pnp3
```

Results recorded inline above.
