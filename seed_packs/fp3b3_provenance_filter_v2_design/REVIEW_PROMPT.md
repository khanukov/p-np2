# Review prompt — fp3b3 Phase 1 sketch review + Phase 2 prompt preparation

> Send this entire file as the prompt body to ONE engineer per
> direction.  Reviewer self-picks `<YOUR-HANDLE>` and is told by
> the dispatcher which `<DIRECTION>` to review.  At most one
> reviewer per direction.  This dispatch round covers V2-A and
> V2-C only; V2-B and V2-D are NOT in this round.

---

You are reviewing ONE Phase 1 paper sketch from
`seed_packs/fp3b3_provenance_filter_v2_design/`.  Your task has
two outputs:

1. A **review document** (verdict + reasoning).
2. **If you approve**: a tailored **Phase 2 prompt** for the
   engineer who will formalise the exclusion theorems.

Pick a unique `<YOUR-HANDLE>`.  Your `<DIRECTION>` is assigned by
the dispatcher (one of: `V2_A_gpt55`, `V2_C_GPT55`).

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN.  Stop and report if RED.

## 1. Required reading (in order)

1. The Phase 1 sketch you're reviewing:
   `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<DIRECTION>/Sketch.lean`.
2. `seed_packs/fp3b3_provenance_filter_v2_design/README.md` —
   especially §3 (per-direction shapes) and the per-phase
   acceptance criteria.
3. `seed_packs/fp3b3_provenance_filter_v2_design/WORKER_PROMPT.md` —
   the contract Phase 2 engineers will use.  Your output Phase 2
   prompt is a tailored specialisation of this.
4. The four kernel-checked obstructions any v2 must clear:
   * `outputs/nogolog.jsonl::NOGO-000001`,
   * `outputs/nogolog.jsonl::NOGO-000004`,
   * `outputs/nogolog.jsonl::NOGO-000005`,
   * `outputs/nogolog.jsonl::NOGO-000006`.
5. **The new fp3b4 meta-barrier (CRITICAL for §3 below):**
   `outputs/nogolog.jsonl::NOGO-000007` and the underlying Lean
   theorem
   `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean::support_cardinality_barrier`
   plus the predicate
   `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/SupportCardinalityOnly.lean::IsSupportCardinalityOnly`.
6. The candidate filter under attack:
   `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3Attempt.InSupportFunctionalDiversity`
   (line 231).
7. The two adversary witnesses your direction's filter must
   exclude in Phase 2:
   * `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3b1.LogWidthAdversary.adversaryWitness_v_natlog2`
     (NOGO-000004 family — prefix-AND on `Nat.log2 (n+1)` window),
   * `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Family.lean::adversaryFamily_v_arbpayload`
     and the corresponding witness in `Witness.lean`
     (NOGO-000006 family — `rename σ_n (ttFormula f_n)` for
     all-essential `f_n`).

## 2. Review checklist (mandatory, all items)

For the assigned `<DIRECTION>`, verify:

- [ ] **Phase 1 file compiles** (already wired in `lakefile.lean`;
      `lake build PnP3` includes it).
- [ ] **Filter `Prop` definition is well-formed** (compiles,
      types check, no `sorry`/`admit`).
- [ ] **`theorem v2_<X>_phase1_loaded : True := trivial`** smoke
      witness present.
- [ ] **Five-paragraph docstring**: explicit paragraphs for
      (i) excludes NOGO-000001, (ii) excludes NOGO-000004/5,
      (iii) excludes NOGO-000006, (iv) non-vacuity (named honest
      family — parity strongly recommended), (v) self-attack.
- [ ] Each paragraph is **non-vacuous prose** — not a one-liner
      "obvious", not Template placeholder.
- [ ] **Forbidden scope respected**: no Lean code outside the
      sketch directory, no NOGO promotion, no JSONL edits, no
      trust-root touches.

## 3. NOGO-000007 self-test (CRITICAL — automatic reject if fails)

`fp3b4` shipped a meta-barrier theorem
`support_cardinality_barrier` (in `SupportCardinalityBarrier/Barrier.lean`)
proving:

> Any filter `Π : ∀ {L}, InPpolyFormula L → Prop` satisfying
> `IsSupportCardinalityOnly Π` is dead-on-arrival: it admits a
> canonical hardwiring twin for any honest sublinear-support
> witness.

Therefore:

> **A v2 candidate satisfying `IsSupportCardinalityOnly` is
> automatically refuted by `support_cardinality_barrier`.  Such a
> candidate cannot survive Phase 2 even in principle.**

Your review's §2 (NOGO-000007 self-test) must answer:

* **Q:** Does the candidate filter
  `ProvenanceFilter_v2_<DIRECTION>` satisfy `IsSupportCardinalityOnly`?
* **A:** Either:
  * **YES** → review verdict is automatically `reject`.
    Document why the filter is support-cardinality-only (e.g.,
    "all conjuncts depend only on `(support …).card`").
    NO Phase 2 prompt produced.
  * **NO** → argue why, citing the specific structural
    information the filter uses beyond support cardinality
    (e.g., gate counts, depth, occurrence counts, recurrence
    relations).  Specify which `InPpolyFormula` field outside
    `family` contributes (e.g., `polyBound`, or some
    syntactic predicate computed from `family n`).  This is
    Phase 2's first kernel-checked theorem to prove.

You don't have to formally prove `¬ IsSupportCardinalityOnly` in
the review — Phase 2 will do that.  You DO have to argue it
plausibly enough that an honest reviewer would accept the claim.

## 4. Non-vacuity assessment

Re-read paragraph (iv) of the docstring.  The author claimed a
specific named honest family the filter admits.  Evaluate:

* **Concrete?** "parity" is concrete; "some honest family" is
  not.
* **Plausible?** Does the filter's shape actually admit the
  claimed family?  Can you sketch an admit-proof?  (You're not
  proving it — just sanity-checking the claim isn't obviously
  false.)
* **Named?** The Phase 2 engineer needs to formalise the
  admit-proof for a SPECIFIC family.  Either the sketch named
  one (good — your review confirms or replaces it), or it didn't
  (bad — your review must propose one).

## 5. Output

### Output A — Review document

Write at:

```
seed_packs/fp3b3_provenance_filter_v2_design/reviews/<DIRECTION>_review_<YOUR-HANDLE>.md
```

Sections (in order):

1. **Verdict.**  ONE of:
   * `approve` — proceed to Phase 2 directly.
   * `approve_with_changes` — Phase 2 may proceed, but the
     reviewer requests specific changes encoded in the Phase 2
     prompt.
   * `reject` — direction is dead.  Provide reason.  No Phase 2
     prompt.
2. **NOGO-000007 self-test.**  Per §3 above.  Must include
   either "support-cardinality-only → REJECT" or a structural
   argument why not.
3. **Non-vacuity assessment.**  Per §4 above.  Includes the
   named family Phase 2 must admit (your final pick).
4. **Five-paragraph review.**  One subsection per docstring
   paragraph (i-v): is it sound?  what's wrong?  what does
   Phase 2 need to clarify?
5. **Phase 2 readiness checklist.**  What Phase 2 must produce,
   in your understanding, after reading this Phase 1 sketch.
   Ties to §1's allowed/forbidden scope.
6. **Risks for Phase 2.**  Honest list of failure modes you
   foresee — circularity, vacuity, kernel-explosion, "trick that
   doesn't generalise", etc.

### Output B — Phase 2 prompt (only if verdict is `approve` or `approve_with_changes`)

Write at:

```
seed_packs/fp3b3_provenance_filter_v2_design/phase2_prompts/<DIRECTION>_phase2.md
```

Use the template at
`seed_packs/fp3b3_provenance_filter_v2_design/phase2_prompts/_TEMPLATE.md`
as starting point.  Fill in:

* The exact named theorems Phase 2 must prove
  (`ExcludesOverbroad_<DIR>`, `ExcludesPrefixAnd_<DIR>`,
  `ExcludesArbitraryPayload_<DIR>`,
  `NonVacuity_<DIR>_admits_<honest_family>`,
  `Survivor_<DIR>`).
* Concrete file paths under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/<DIRECTION>/`.
* Required imports (existing modules + theorems Phase 2 should
  reuse — fp3b1's `prefixAnd_*`, fp3b2's
  `adversaryFamily_v_arbpayload_support_card`, fp3b4's
  `support_cardinality_barrier`).
* Direction-specific traps (from your §6).
* The named honest family for non-vacuity (parity unless your
  §3 picked something else).

## 6. Forbidden

* **Editing the Phase 1 sketch.**  Review only — no edits.
* Editing other directions' files
  (`<other-direction>/`).
* Editing the seed pack's `README.md`, `WORKER_PROMPT.md`, or
  `failures/` — those are stable.
* Editing `lakefile.lean`, NOGO entries, attempt entries.
* Trust root (Rule 0).
* `sorry`/`admit` in any committed Lean.
* `pnp3/Candidates/`, `gap_from_*`, `SourceTheorem_*`, final
  endpoint, `ProvenanceFilter_v1` promotion, Wave 1 force.
* Promoting any v2 to "accepted" — review only verifies
  Phase 2 readiness; promotion is a much later step.

## 7. Acceptance criteria

A review delivery is accepted when:

- [ ] Output A document exists with all 6 required sections.
- [ ] Output B exists iff verdict is `approve` or
      `approve_with_changes`, and Output B uses the
      `_TEMPLATE.md` shape filled in.
- [ ] §2 (NOGO-000007 self-test) gives a definite answer
      (yes/no + reasoning).
- [ ] §3 (non-vacuity) names a SPECIFIC family.
- [ ] No file outside §5 output paths is modified.
- [ ] `lake build PnP3` and `scripts/check.sh` stay green
      (review is documentation; nothing should regress).

A review delivery is rejected when:

* Verdict is `approve` but §2 says the filter IS
  support-cardinality-only (contradicts NOGO-000007).
* Verdict is `approve` but §3 fails to name a family.
* Output B is missing when verdict is `approve` or
  `approve_with_changes`.

## 8. Begin

1. Pick `<YOUR-HANDLE>`.
2. Verify green baseline.
3. Read your assigned `<DIRECTION>` Phase 1 sketch + §1
   materials.
4. Apply §2 checklist.
5. Run §3 self-test.  This determines verdict.
6. Run §4 non-vacuity assessment.
7. Write Output A.
8. If verdict is approve(_with_changes), write Output B from
   the template.
9. Commit + push.  Stop.

End of prompt.
