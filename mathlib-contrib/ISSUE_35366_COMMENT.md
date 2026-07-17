# Draft comment for mathlib4 issue #35366

> ⚠️ **НЕ копируй этот текст в issue дословно.** Политика mathlib прямо
> запрещает LLM-написанные комментарии на GitHub и Zulip: *"Using an LLM
> when writing comments on GitHub or Zulip is not allowed: use your own
> words"* (https://leanprover-community.github.io/contribute/index.html).
> Текст ниже — только фактическая шпаргалка. Напиши комментарий сам, своими
> словами и лаконичнее; факты (что реализовано, ответы на три вопроса
> issue, ссылка на файл) бери отсюда. Раскрытие использования ИИ для самого
> кода делается в описании PR — оно там уже есть.

---

I have a complete, compiling implementation of this proposal against current
mathlib (verified on `v4.30.0`), with answers to the three open design
questions and one addition beyond the original scope. Happy to open it as a
PR (or a PR stack) if the direction looks right. File:
[`TM1Complexity.lean`](https://github.com/khanukov/p-np2/blob/claude/p-vs-np-approaches-q6p57c/mathlib-contrib/TM1Complexity.lean)
(511 lines, no `sorry`, standard axioms only, no new imports beyond
`PostTuringMachine` + a proof-only `Fintype.Basic`).

**On the three questions in the issue:**

1. *TM1 or coordinate with #33132 (FinTM0)?* — This stays on TM1 as proposed
   here, and I believe the two are complementary rather than competing:
   #33132 gives a bundled single-tape model with relational timing; this
   gives step counting and classes for the existing TM1. A bridge theorem
   between them is natural follow-up work either way, so neither blocks the
   other.

2. *Fuel-based `runN` vs relational?* — Both, with an equivalence theorem.
   `runN` (fuel-based, absorbing at halt) is the workhorse — time-bound
   statements become plain equalities, and monotonicity is
   `runN_add`/`runN_le`. The bridge lemma

   ```lean
   theorem mem_eval_iff_exists_runN :
       b ∈ StateTransition.eval (step M) c ↔ (∃ n, runN M n c = b) ∧ b.l = none
   ```

   proves it agrees with the existing relational semantics, so this does not
   fork the notion of evaluation.

3. *Separate file for `IsPolynomial`?* — I used a deliberately lightweight
   `IsPolyTimeBound T : ∃ k, ∀ n, T n ≤ n ^ k + k` local to the file. Using
   `Polynomial ℕ` would drag algebra imports into the computability
   hierarchy (`PostTuringMachine` has `assert_not_exists MonoidWithZero`);
   if maintainers prefer a shared home for growth-rate predicates, it can
   move later without changing any statement downstream.

**Two design points where I strengthened the original sketch:**

* **Finite control is part of the class definition.** `InP`/`InNP` quantify
  over machines with `Fintype` label and store types (via `PTimeDecider` /
  `PTimeVerifier` structures with instance fields). This is load-bearing,
  not decoration: with an infinite label/store type, a single transition can
  smuggle unboundedly much information and the "class" degenerates.

* **Beyond the issue's scope: P is closed under complement.**

  ```lean
  theorem InP.compl (h : InP Γ accept L)
      (ha : ∃ a, accept a) (hr : ∃ r, ¬accept r) : InP Γ accept Lᶜ
  ```

  The textbook "swap accept and reject" becomes a statement transformation
  `Stmt.mapHalt` (`halt ↦ write flip halt`) with a simulation lemma; since
  only `goto`/`halt` consume steps in TM1, the complement machine runs in
  *exactly* the same time bound. `InP.subset_np` (P ⊆ NP) is also included,
  using the pleasant fact that tapes are quotients by trailing blanks, so a
  decider is literally a verifier for empty certificates.

Also included: `step_eq_none_iff`, `haltedAt`-style stability lemmas, a
one-step inhabitation witness for `InP`, and `DecidesInTime.mono` (enlarging
the clock never changes the verdict).

If this looks right I would split it as: PR 1 — `runN` + bridge to
`StateTransition.eval`; PR 2 — `DecidesInTime`/`IsPolyTimeBound`; PR 3 —
classes, P ⊆ NP, complement closure. Feedback on naming and placement
(`Mathlib/Computability/TuringMachine/TM1Complexity.lean`) very welcome.
