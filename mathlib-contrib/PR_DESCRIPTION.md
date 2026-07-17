# Draft mathlib4 PR description

**Title:** `feat(Computability/TuringMachine): add step counting and complexity classes P/NP for TM1`

> Перед отправкой: прочитай тело ниже и поправь под себя — ты должен стоять
> за каждым словом. После открытия PR обязательно оставь комментарий
> `LLM-generated` (одним словом) — это добавит требуемую политикой метку.
> Проверь, что base = `leanprover-community/mathlib4` `master` (не master
> твоего форка).

---

Implements the proposal of #35366 for the TM1 model, and additionally proves
that P is closed under complement.

## Main definitions

* `Turing.TM1.runN`: fuel-based execution of a TM1 machine (absorbing at the
  halting configuration), with a stability/monotonicity toolkit
  (`runN_of_halted`, `runN_add`, `runN_le`).
* `Turing.TM1.AcceptsIn`, `Turing.TM1.DecidesInTime`: time-bounded
  acceptance/decision, with acceptance read off the tape symbol under the
  head in the halting configuration (`accept : Γ → Prop`).
* `Turing.TM1.IsPolyTimeBound`: lightweight polynomial growth bounds
  (`∃ k, ∀ n, T n ≤ n ^ k + k`), avoiding algebra imports in the
  computability hierarchy.
* `Turing.TM1.PTimeDecider`, `Turing.TM1.PTimeVerifier`,
  `Turing.TM1.InP`, `Turing.TM1.InNP`: the complexity classes P and NP over
  an alphabet `Γ`, quantifying over machines with finite (`Fintype`) label
  and store types.
* `Turing.TM1.Stmt.mapHalt`: statement transformation replacing every `halt`
  by `write f halt` (used for the complement construction).

## Main results

* `Turing.TM1.mem_eval_iff_exists_runN`: the fuel-based semantics agrees
  with the existing relational semantics `StateTransition.eval`.
* `Turing.TM1.DecidesInTime.mono`: enlarging the time bound preserves the
  decision (the sampling moment is irrelevant).
* `Turing.TM1.inP_head`: `InP` is inhabited (a one-step machine).
* `Turing.TM1.InP.subset_np`: **P ⊆ NP**.
* `Turing.TM1.InP.compl` / `Turing.TM1.inP_compl_iff`: **P is closed under
  complement** (with the same time bound: `write` costs zero steps in the
  TM1 cost model), assuming the acceptance predicate is non-degenerate.

## Design notes

* Fuel-based execution is used for the resource-bounded layer because time
  bounds become equalities; the bridge lemma keeps it consistent with the
  relational `eval`, so there is a single notion of evaluation.
* Finiteness of the control (`Fintype` label/store) is part of the class
  definitions; without it the classes degenerate.
* The certificate convention in `InNP` (`l ++ default :: c`) exploits that
  tapes are quotients by trailing blanks: `init (l ++ [default]) = init l`,
  which makes a decider literally a verifier for empty certificates.

Closes #35366.

## AI usage disclosure

The Lean code in this PR was written with substantial assistance from an LLM
(Anthropic's Claude, via Claude Code), working under my direction from the
design sketch in issue #35366, over several design iterations. I have
reviewed the file and understand the definitions and proofs. The file was
verified by compiling it against mathlib `v4.30.0` (kernel-checked;
`#print axioms` reports standard axioms only) and re-checked against current
`master` for API drift before opening this PR. Per the contribution
guidelines I am adding the `LLM-generated` label.
