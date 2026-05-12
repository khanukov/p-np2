# Operator review — fp3b3 V2-C/GPT55 Phase 2 start

> **Reviewer:** operator (independent of engineer and Phase 1 reviewer).
> **Subject:** fp3b3 V2-C Phase 2, commit `b6ecce6` ("Start V2-C phase 2 audit harness").
> **Question:** is V2-C Phase 2 complete enough to seek promotion to
> `spec/known_guards.toml::ProvenanceFilter_v2` informal status (the way V2-A
> just was at `66a900a`), or to be otherwise integrated as a survivor?
> **Authority of this review:** advisory.

## TL;DR

**Verdict: `partial_phase2_start` — NOT a survivor; promotion path BLOCKED.**

V2-C Phase 2 shipped exactly one mechanical theorem family (a general
zero-extension rejection harness + one toy smoke-test exclusion) and zero of
the seven mandatory deliverables enumerated in
`phase2_prompts/V2_C_GPT55_phase2.md` §2/§3.  In addition, the commit edits
`Sketch.lean` in place, which is explicitly forbidden by the Phase 2 prompt
§5 ("Editing the Phase 1 sketch").

The work that WAS shipped is mathematically clean — the rejection harness is
a sound, kernel-checked consequence of the Phase 1 predicate, and the smoke-
test exclusion really does fail the zero-extension law at `0 → 1`.  But this
is starter scaffolding, not a survivor.  V2-C is currently neither in
**Outcome A** (full survivor candidate) nor in **Outcome B** (structured
failure report); it is in an unresolved third state which the prompt did not
authorise.

The integrator should choose one of three follow-up paths (§5 of this
review).

## 0. Sanity preamble

* `lake build PnP3 Pnp4` — green at `66a900a`.
* `scripts/check.sh` — 17/17 + sub-steps green.
* `rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_C_GPT55/`
  — clean (the directory contains a single file, `Sketch.lean`).
* `validate_jsonl.py outputs/{nogolog,attempts}.jsonl` — OK.
* No JSONL line was edited (Rule 9 honoured).
* No trust-root edit.
* No `pnp3/Candidates/<id>/` introduced.
* No FP-4 / SourceTheorem / `gap_from_*` / final endpoint introduced.

Sanity: PASS.  Proceeds to substantive review.

## 1. Gap analysis vs the Phase 2 prompt contract

The Phase 2 prompt (`phase2_prompts/V2_C_GPT55_phase2.md`) is explicit
about file layout (§2) and required theorem signatures (§3).  Comparing
against `b6ecce6`:

| Required file | Required theorem | Status in `b6ecce6` |
| ---           | ---              | ---                 |
| `Filter.lean` | re-export `ProvenanceFilter_v2_V2_C_GPT55` | **MISSING** (no file) |
| `NotSupportCardinalityOnly.lean` | `ProvenanceFilter_v2_V2_C_GPT55_not_support_cardinality_only` | **MISSING** |
| `ExcludesOverbroad.lean` | `excludes_overbroad_V2_C_GPT55` (NOGO-000001) | **MISSING** |
| `ExcludesPrefixAnd.lean` | `excludes_prefixAnd_V2_C_GPT55` (NOGO-000004/000005) | **MISSING** |
| `ExcludesArbitraryPayload.lean` | `excludes_arbitrary_payload_V2_C_GPT55` (NOGO-000006) | **MISSING** |
| `NonVacuity.lean` | `orAll_witness` + `V2_C_GPT55_admits_orAll` | **MISSING** |
| `Survivor.lean` | `ProvenanceFilter_v2_V2_C_GPT55_survives_known_obstructions` | **MISSING** |

Score: **0/7 mandatory theorem surfaces.**

What IS in `Sketch.lean` (post-commit):

* `v2_C_GPT55_rejects_of_zeroExtension_counterexample` — general
  rejection harness, not in the required name set but **mathematically useful
  scaffolding** (any one zero-extension counterexample rejects the witness).
* `badOneStepFamily` / `badOneStepLanguage` / `badOneStepWitness` — a tiny
  one-step toy family where length `0` is `const true` and length `≥ 1` is
  `input 0`.  Concrete, not a hardwiring witness.
* `badOneStep_zeroExtension_counterexample` — the specific `0 → 1` failure.
* `v2_C_GPT55_rejects_badOneStep` — the smoke-test exclusion application.
* `v2_C_GPT55_phase2_loaded : True := trivial` — smoke witness.

None of these is one of the three NOGO exclusion targets
(NOGO-000001/4/5/6) the prompt requires, nor the NOGO-000007 dodge, nor the
honest-family non-vacuity proof.  They are early-Phase-2 scaffolding only.

## 2. Scope violation: in-place edit of Phase 1 Sketch.lean

The Phase 2 prompt §5 **Forbidden** list says verbatim:

> * Editing the Phase 1 sketch.

The Phase 1 sketch is `Sketch.lean` at commit `2b9eb47`.  Commit `b6ecce6`
modifies that exact file (`94 insertions(+), 11 deletions(-)`).  The diff
contents:

1. **Header rewrite:** "Phase 1 sketch" → "Phase 2 audit start" and a
   companion change of progress-classification tagline.  Cosmetic but is a
   prose edit to a file the prompt locks.
2. **Docstring rewrite:** five `**Excludes NOGO-...**` headings demoted to
   `**Phase-1 intended exclusion target: NOGO-...**`.  These are
   **honest downgrades** — the original "Excludes" claim was prose-only at
   Phase 1 and the downgrade more accurately reflects audit status.
   Substantively a good change; procedurally a forbidden edit.
3. **`v2_C_GPT55_phase1_loaded`** smoke removed and `v2_C_GPT55_phase2_loaded`
   added at the bottom.  Both are `True := trivial`.
4. **Append at end of file:** the new harness + smoke-test family + smoke-test
   exclusion theorems (≈ 80 LOC).

Severity assessment:

| Aspect | Severity | Why |
| ---    | ---      | --- |
| Prose-only docstring edits | LOW | Improvements in honesty; reversible. |
| Renaming `phase1_loaded` → `phase2_loaded` | LOW | One-line cosmetic. |
| Adding ≈ 80 LOC of new theorems to Sketch.lean | MEDIUM | Should have been in a new `Filter.lean` (Phase 2 prompt §2 explicit file layout). |
| Net contract violation | MEDIUM | The prompt's "do not edit Phase 1 sketch" exists precisely to keep Phase 2 review focused on a NEW file surface; merging Phase 1 + Phase 2 in one file complicates future review and rollback. |

This violation does NOT make the kernel-checked content unsound.  It does
make the engineer's submission not conformant to the prompt.

## 3. What WAS shipped — independent kernel re-check

### 3.1 `v2_C_GPT55_rejects_of_zeroExtension_counterexample`

`Sketch.lean:108`.

**Statement:**

```lean
∀ {L : Language} (w : InPpolyFormula L) (n : Nat) (x : Bitstring n),
  (eval (w.family (n+1)) (zero-pad x at coord n) ≠ eval (w.family n) x) →
  ¬ ProvenanceFilter_v2_V2_C_GPT55 w
```

**Proof shape:** destructure `⟨δ, _hsize, hzero⟩`; apply `hzero n x` to
contradict `hbad`.

**Soundness:** trivially kernel-checked; one-line proof.  Sound.

**Value as scaffolding:** real value.  Any Phase 2 exclusion of a concrete
family that fails zero-extension at one length transition can be discharged
by this harness in one line.

**Limitation:** does NOT, on its own, exclude any of the three NOGO
hardwiring shapes the prompt requires.  Each of the three exclusions still
needs (a) an explicit `n` and `x`, (b) a kernel-checked proof that the
specific family's zero-extension fails at `(n, x)`.

### 3.2 `badOneStepFamily` / `badOneStepWitness`

`Sketch.lean:129`, `Sketch.lean:138`.

**Definition:** `family 0 = const true`, `family (n+1) = input 0`.  Polynomial
bound `1` (which is OK because each formula has size `1`).

**Stress test — is this family a real adversary?**  No.  It is a
deliberately tiny smoke-test counterexample, not a hardwiring shape.  The
size profile is `(1, 1, 1, …)`; this is below any meaningful hardwiring
budget.  The function computed is `true` at length 0 and `proj_0` at every
positive length — semantically discontinuous at `0 → 1`, which is what
makes it a one-step zero-extension counterexample.

**Verdict:** sound; demonstrates the harness fires; does NOT contribute to
the survivor surface required by the prompt.

### 3.3 `v2_C_GPT55_rejects_badOneStep`

`Sketch.lean:167`.

One-line application of `v2_C_GPT55_rejects_of_zeroExtension_counterexample`
with `n=0` and `x=emptyBits`.  Sound.

### 3.4 What did NOT ship — concrete misses

The three exclusions the prompt names — NOGO-000001 fixed-slice,
NOGO-000004/5 prefix-AND, NOGO-000006 arbitrary all-essential payload —
**all involve nontrivial length-transition work**:

* **NOGO-000001** needs a fixed-slice hardwiring witness with `ttFormula` at
  `partialInputLen p` and `const false` elsewhere.  The zero-extension law
  fails at the `partialInputLen p → partialInputLen p + 1` transition iff
  there is some input with disagreeing eval.  This is the kind of theorem the
  shipped harness can discharge in a few lines once the specific transition
  + witness input is exhibited.  Not exhibited.
* **NOGO-000004/5** needs `widthFn` increase from `k` to `k+1` for the
  prefix-AND family.  Concrete `n` where `logWidthNat(n) < logWidthNat(n+1)`
  and an old input with all-true prefix where the newly included prefix
  coordinate is false.  Not exhibited.
* **NOGO-000006** needs `widthFn` increase and an all-essential argument
  applied at the fresh prefix coordinate.  Not exhibited.

Each of the three would slot cleanly into the existing harness, but the
work of locating the right `n` + `x` and assembling the eval-mismatch proof
has not been done.

The two highest-risk items also have NOT been addressed:

* **`not_support_cardinality_only`** — NOGO-000007 dodge.  No exhibition of
  two witnesses with identical support cardinality and different filter
  membership.  Phase 1 reviewer (`reviews/V2_C_GPT55_review_codex55c.md` §2)
  argued the dodge should hold, but Phase 2 must prove it.  Not proved.
* **`orAll` non-vacuity** — no `orAllFormula`, no `orAll_witness`, no
  `V2_C_GPT55_admits_orAll`.  Without this, V2-C is structurally at risk of
  the vacuity attack (Critic Attack 6) — if no concrete family is admitted,
  the filter is potentially equivalent to `False`.

## 4. Six-attack independent re-review (partial)

Because the Phase 2 deliverables are largely missing, the Critic six-attack
re-review is also incomplete.  I record the partial signal:

### Attack 1 — Hidden-payload

**Status:** `no break found` for the currently-shipped surface.  No `class`,
`instance`, `Fact`, `opaque`, `axiom`, `native_decide` in `Sketch.lean`.
`badOneStepWitness` uses `polyBound = fun _ => 1`, `correct = fun _ _ => rfl`
— concrete, no payload smuggling.

### Attack 2 — Hardwiring

**Status:** `attack not yet addressed`.  None of the three hardwiring NOGO
exclusions has been formalised.  The general harness is in place but its
applications are not.  Until the three named exclusions ship, the filter is
not demonstrated to reject the canonical hardwiring shapes — the Phase 2
prompt's core obligation.

### Attack 3 — KnownGuards-factorization

**Status:** `no break found`, but mostly vacuously: the filter does not yet
appear in any factorisation chain because Survivor.lean does not exist.

### Attack 4 — Natural-proof / relativization / algebrization

**Status:** `attack not applicable` for an audit predicate; same posture as
V2-A.  The barrier check would only become live on any promotion path beyond
`informal`.

### Attack 5 — Collapse-not-contradiction

**Status:** `no break found`.  The shipped exclusion theorem has `False`
conclusion; no class-collapse claims.

### Attack 6 — Vacuity / source-theorem rephrasing

**Status:** **OPEN RISK.**  The filter has NO admitted family.  Specifically:

* `badOneStepWitness` is REJECTED by the filter (that is the point of
  `v2_C_GPT55_rejects_badOneStep`).
* No `orAll` family is constructed.
* No other family is exhibited as admitted.

The Phase 2 prompt §3.6 mandates `V2_C_GPT55_admits_orAll`.  Without it the
six-attack vacuity check is **not passable**.  This is the single most
important gap from a Critic standpoint: without non-vacuity, V2-C could be
equivalent to `False` on `InPpolyFormula`, in which case all three
"exclusions" would be vacuously true.

## 5. Recommended next actions

Three coherent paths the integrator can take.  Choose ONE.

### Path A — Re-dispatch V2-C Phase 2 to finish

A new engineer takes the existing `Sketch.lean` as Phase 1 (in spite of the
edit), and produces the remaining six files
(`Filter.lean`, `NotSupportCardinalityOnly.lean`, `ExcludesOverbroad.lean`,
`ExcludesPrefixAnd.lean`, `ExcludesArbitraryPayload.lean`, `NonVacuity.lean`,
`Survivor.lean`) per the existing Phase 2 prompt.  The new engineer may
**reuse** `v2_C_GPT55_rejects_of_zeroExtension_counterexample` as the
shared harness for all three exclusions — that work is real and useful.

Cost: roughly the same as a fresh Phase 2 dispatch, minus the harness.
Benefit: a parallel V2-survivor to V2-A.

### Path B — Demote V2-C to "structured failure" + close the direction

If on closer inspection V2-C cannot dodge NOGO-000007 cleanly (Phase 1
reviewer thought it could, but Phase 2 did not formalise it), or if the
true-slice payload risk noted in `reviews/V2_C_GPT55_review_codex55c.md` §6
turns out to be insurmountable, write the structured failure report at
`seed_packs/fp3b3_provenance_filter_v2_design/failures/V2_C_GPT55_phase2.md`
per the Phase 2 prompt §7 Outcome B template, and stop work on V2-C.  Keep
the existing harness in `Sketch.lean` as audit-only scaffolding.

Cost: small writeup.  Benefit: a clean negative result that
informs V2-B/V2-D dispatch.

### Path C — Accept the incomplete state as "Phase 2 partial start", proceed
to V2-B / V2-D in parallel

Leave V2-C as it stands.  Make no promotion claim.  Dispatch V2-B and V2-D
Phase 2 engineers.  If either V2-B or V2-D produces a full survivor, that
becomes the second `informal` ProvenanceFilter_v2 candidate; V2-C remains in
its partial state until it is either revived (Path A) or closed (Path B).

Cost: parallel work continues; V2-C accumulates as half-shipped status.
Risk: half-shipped state tends to confuse future reviewers; the
"do not edit Phase 1 sketch" scope violation is left unaddressed.

### Operator's recommendation

**Path A (re-dispatch to finish)** is the highest-EV choice.  The
mathematical groundwork is partly done (general harness exists), and a
finished V2-C would provide a second `ProvenanceFilter_v2` survivor with a
**different shape** from V2-A (cross-length semantic vs single-length
gate-count), which is valuable insurance against the hidden-payload /
syntactic-rewrite caveat documented in `V2_A_gpt55_promotion_review.md` §3.
If Path A's engineer hits a true blocker, they downgrade to Path B in-flight.

## 6. Promotion path verdict

**Recommended verdict: `do_not_promote` — V2-C is not eligible for any
`spec/known_guards.toml` entry at this time.**

Specifically:

* V2-C does NOT meet the prompt's Outcome A bar (full survivor candidate).
* V2-C has not produced an Outcome B structured failure either.
* V2-C cannot be promoted to `ProvenanceFilter_v2_alt` or any sibling name
  in `spec/known_guards.toml` until at least:
  1. `not_support_cardinality_only` is kernel-checked (NOGO-000007 dodge);
  2. one of the three NOGO exclusions is kernel-checked (not the toy
     `badOneStep` smoke);
  3. `orAll_witness` non-vacuity is kernel-checked (Critic Attack 6 hard
     bar).
* Even after those three, the four-caveat severity assessment from V2-A
  applies to V2-C as well; V2-C would enter as `informal`, not `accepted`.

V2-A remains the only `ProvenanceFilter_v2` entry in `spec/known_guards.toml`,
unchanged by this review.

## 7. Audit trail

* `b6ecce6` `pnp3/.../V2_C_GPT55/Sketch.lean` — read in full.
* `phase2_prompts/V2_C_GPT55_phase2.md` — read in full.
* `reviews/V2_C_GPT55_review_codex55c.md` — read in full.
* `git diff 2b9eb47 b6ecce6 -- pnp3/.../V2_C_GPT55/Sketch.lean` — inspected
  to localise the scope violation.
* Pipeline rerun: `lake build PnP3 Pnp4` + `scripts/check.sh` — both green
  (the partial Phase 2 work IS clean Lean; the issue is incompleteness, not
  unsoundness).
* No edits to V2-C files were made during this review.  This document is
  the only artifact produced.

## 8. Closing note

> V2-C Phase 2 is a **competent partial start**, not a finish.  The shipped
> general rejection harness is real scaffolding and can be reused; the toy
> smoke-test exclusion proves the harness fires.  But none of the three
> NOGO hardwiring exclusions has been formalised, the NOGO-000007 dodge has
> not been kernel-checked, and the honest-family non-vacuity is missing.
> Promotion of V2-C is BLOCKED.  Re-dispatch to finish (Path A) is the
> recommended next step; Outcome B failure report (Path B) is the
> fallback.  V2-A remains the sole `ProvenanceFilter_v2` informal entry.
