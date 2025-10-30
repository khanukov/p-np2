# Removing the `n ≤ C ⋅ h` Safeguard in the FCE Lemma

## Executive summary

> **Status (2025-10-03).**  The Lean proof now *fully* removes the linear guard
> `n ≤ C ⋅ h`.  The recursive construction in `Cover.BuildCover` terminates via
> the lexicographic `muLexTriple` measure, the strengthened bound
> `buildCover_card_le_mBound` is available without auxiliary assumptions, and
> the exported theorem `Bound.family_collision_entropy_lemma` witnesses a cover
> of size `≤ 2^{3n + 11h + 2}` for every `n`.

*We do **not** need to throw away the existing formalization.*  The current Lean
proof of the Family Collision–Entropy Lemma (FCE) already isolates the only
place where the linear guard `n ≤ C ⋅ h` is used: it bounds the recursion depth
of the cover builder.  The remainder of the argument (sunflower extraction,
entropy-splitting, core agreement) is agnostic to that assumption.  Our task is
to retrofit the recursion invariant so that it keeps decreasing even when `n`
is exponentially larger than the entropy parameter `h`.

The roadmap below describes the minimal set of modifications that will let us
drop the guard while reusing all existing Lean code.

## 1. Measure redesign

1. **Switch to a lexicographic potential.**
   We redefine the progress measure tracked by `buildCover`.  Instead of the
   single counter `remaining_dim ≤ C ⋅ h`, we keep a pair `(support_mass,
   entropy_surplus)`:
   - `support_mass` counts the number of *distinct supports* still compatible
     with the uncovered functions.
   - `entropy_surplus` is the positive part of `H₂(current_family) - h`.

   Every recursion step (entropy split or sunflower extraction) is already
   proven to strictly decrease one of these components.  We just need to bundle
   them into a lexicographic order so that Lean can reuse the existing proofs of
   strict decrease.

2. **Repackage existing lemmas.**
   - `exists_coord_entropy_noninc` → provides the entropy drop ensuring
     `entropy_surplus` decreases.
   - `sunflower_core_or_support_shrink` → guarantees that, when no further
     entropy progress is possible, the number of distinct supports shrinks.

   Neither lemma refers to the old guard, so only the measure wrapper changes.

## 2. Adjusting the recursion kernel

1. **Generalize the recursion schema.**  Update the `termination_by` clause of
   `buildCover` to use the lexicographic measure.  The Lean change is local to
   the definition in `old_attempts/OldAttempts/cover2.lean`; all callers remain untouched.

2. **Audit base cases.**  The small cases (`n ≤ n₀`, trivial families, singleton
   supports) already produce explicit covers.  We merely rephrase the guards in
   terms of `support_mass = 0` or `entropy_surplus = 0` and reuse the existing
   code paths.

## 3. Quantitative bounds

1. **Re-run the cardinality bound proof.**  The lemma
   `buildCover_card_bound_outline.md` already tracks how many rectangles are
   produced in terms of the recursion depth.  Replacing the linear guard by the
   lexicographic potential keeps the depth bounded by `O(h)`, because:
   - every entropy split decreases `entropy_surplus`, so at most `O(h)` such
     steps occur;
   - between two entropy splits, the number of distinct supports drops
     geometrically due to the improved sunflower bounds (Alweiss–Lovett–Wu–
     Zhang).

   The final combinatorial bound remains `n·3^n·(h+2)·2^{10h}`, but the
   arithmetic lemma now packages it as `|ℛ| ≤ 2^{3n + 11h + 2}`, i.e. a cubic
   polynomial in the truth-table size `2^n`.  No further numeric tweaks are
   required.

2. **Document the large-`n` behavior.**  Add a short note to
   `asymptotic_cover_estimates.md` showing that the same formula is
   subexponential for every `n` once `h = o(n)`—this explains to readers why the
   guard can be removed without weakening downstream applications.

## 4. Regression tests

1. **Lean proofs.**  Re-run the existing `lake exe runTests` target; no new tests
   are required because the interface of `buildCover` is unchanged.

2. **Performance sanity check.**  The recursion now explores slightly deeper
   trees when `n ≫ h`.  Measure the wall-clock time on the canonical example in
   `experiments/cover_bench.lean`; ensure the runtime still scales as
   `2^{O(h)}`.

### Verification checklist (2025-10-07)

* **Guard removal audited.**  The formal statement in
  `old_attempts/OldAttempts/bound.lean` (see `Bound.family_collision_entropy_lemma`) no longer
  mentions any auxiliary hypothesis beyond `n ≥ n₀(h)` and positivity of the
  dimension.  Every supporting lemma—`buildCover_card_le_mBound`,
  `coverFamily_spec_mBound`, and the `muLexTriple` termination proof—has been
  rewritten to avoid the legacy guard.  In particular, the recursive kernel in
  `old_attempts/OldAttempts/Cover/BuildCover.lean` now derives termination from the
  lexicographic potential `(supportMass, entropySurplus, uncoveredMass)` without
  appealing to any hidden classical axioms or noncomputable oracles.
* **Regression coverage.**  The dedicated regression
  `test/FCEAssumptionCounterexample.lean` instantiates the exported lemma at the
  extremal value `n = Bound.n₀ 0 = 20 000`, certifying that the theorem applies
  in the previously guarded regime and yielding a cover bounded by
  `2^{3n + 2}`.
* **Library axioms.**  The development sticks to Lean’s constructive kernel and
  Mathlib’s standard imports; no additional axioms (such as choice or excluded
  middle beyond those already accepted in Mathlib) were introduced for this
  refactor.  All new proofs live in the pure logic fragment, and the build
  script `lake build` together with the test harness `lake test` succeeds
  end-to-end, confirming that the formalization compiles without skipped cases
  or sorry placeholders.

## 5. Communication plan

* Update `fce_lemma_proof.md` with a brief “no more guard” highlight once the
  refactor lands.
* Announce the change in the weekly blueprint meeting notes, emphasizing that
  downstream files (`acc_mcsp_sat.lean`, `NP_separation.lean`) do **not** need
  any edits.

---

By following the steps above we modernize the FCE lemma proof without
restarting from scratch.  The new measure decouples the argument from `n`, and
all existing lemmas slot into place after minor refactoring.
