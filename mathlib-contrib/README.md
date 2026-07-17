# mathlib4 contribution: TM1 step counting and P/NP (issue #35366)

A complete, kernel-checked implementation of what
[mathlib4 issue #35366](https://github.com/leanprover-community/mathlib4/issues/35366)
asks for — plus one result beyond the issue's scope: **P is closed under
complement**, with zero time overhead.

**File:** `TM1Complexity.lean` (511 lines), destined for
`Mathlib/Computability/TuringMachine/TM1Complexity.lean`.

**Status (2026-07-17):** pushed to the fork as branch
[`tm1-complexity`](https://github.com/khanukov/mathlib4/tree/tm1-complexity)
(single commit authored by Dmitry Khanukov, subject
`feat(Computability/TuringMachine): add step counting and complexity classes
P/NP for TM1`, module registered in `Mathlib.lean`); the used API was
re-checked against `master` as of 2026-07-16.  The PR description draft in
`PR_DESCRIPTION.md` contains the AI-usage disclosure required by mathlib's
contribution guidelines; after opening the PR, add the `LLM-generated` label
(by commenting `LLM-generated`).  Issue/Zulip comments must be written in the
author's own words — `ISSUE_35366_COMMENT.md` is a facts-only crib, not text
to paste.

**Verified against:** mathlib4 tag `v4.30.0`
(commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`), toolchain
`leanprover/lean4:v4.30.0`. Zero `sorry`/`admit`/`axiom`/`native_decide`;
every declaration depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); zero linter warnings under
mathlib's in-build style linters.

## What is inside

| Declaration | Content |
|---|---|
| `Turing.TM1.step_eq_none_iff` | `step M c = none ↔ c.l = none` |
| `Turing.TM1.runN` | fuel-based execution (absorbs at halt) |
| `runN_of_halted`, `runN_add`, `runN_le` | fuel monotonicity/stability toolkit |
| `Turing.TM1.mem_eval_iff_exists_runN` | **bridge**: fuel semantics ≡ mathlib's relational `StateTransition.eval` |
| `Turing.TM1.AcceptsIn`, `DecidesInTime`, `DecidesInTime.mono` | time-bounded decision; robustness under enlarging the clock |
| `Turing.TM1.IsPolyTimeBound` | lightweight polynomial bounds (`T n ≤ n ^ k + k`), no algebra imports |
| `Turing.TM1.PTimeDecider`, `PTimeVerifier`, `InP`, `InNP` | the classes, with **`Fintype` finite control** (load-bearing: with infinite label/store types the classes degenerate) |
| `Turing.TM1.inP_head` | inhabitation witness: a 1-step machine decides `{l \| accept l.headI}` |
| `Turing.TM1.InP.subset_np` | **P ⊆ NP** (certificate bound `0`; uses `init (l ++ [default]) = init l` — tapes are quotients by trailing blanks) |
| `Turing.TM1.Stmt.mapHalt`, `stepAux_mapHalt`, `runN_mapHalt` | the halt-rewriting compiler `halt ↦ write flip halt` and its simulation lemmas |
| `Turing.TM1.DecidesInTime.compl`, `InP.compl`, `inP_compl_iff` | **P closed under complement / P = coP**, with the *same* time bound (`write` costs 0 steps in TM1) |

## How to verify (standard mathlib workflow)

```bash
git clone --branch v4.30.0 --depth 1 https://github.com/leanprover-community/mathlib4
cd mathlib4
cp <this dir>/TM1Complexity.lean Mathlib/Computability/TuringMachine/TM1Complexity.lean
lake exe cache get Mathlib/Computability/TuringMachine/PostTuringMachine.lean \
                   Mathlib/Data/Fintype/Basic.lean
lake build Mathlib.Computability.TuringMachine.TM1Complexity
```

Axiom audit (expected output: only `[propext, Classical.choice, Quot.sound]`
for every name):

```lean
import Mathlib.Computability.TuringMachine.TM1Complexity
#print axioms Turing.TM1.mem_eval_iff_exists_runN
#print axioms Turing.TM1.InP.subset_np
#print axioms Turing.TM1.InP.compl
```

## Design decisions (and why)

1. **Fuel-based `runN` *and* the relational semantics.**  The issue asked
   whether maintainers prefer fuel-based or relational execution.  This file
   answers "both": `runN` is the workhorse (time bounds become plain
   equalities), and `mem_eval_iff_exists_runN` proves it equivalent to the
   existing `StateTransition.eval`, so nothing forks the semantics.
2. **Acceptance as a predicate on the head symbol** (as proposed in the
   issue): TM1 has no accept states; the classes are parameterized by
   `accept : Γ → Prop`.
3. **Finite control is required, not decoration.**  `InP`/`InNP` quantify
   machines with `Fintype` label and store types.  Without this the classes
   collapse (an infinite-state "machine" can smuggle arbitrary information
   through one transition).  This lesson was learned the hard way in the
   `p-np2` project: its frozen `P` admits undecidable languages through an
   unconstrained machine-level clock field.
4. **The clock is external to the machine** — `DecidesInTime` takes the bound
   as a parameter and `DecidesInTime.mono` makes the sampling moment
   irrelevant.  This is the second lesson from the same audit.
5. **The complement construction is the textbook proof, made precise.**
   "Swap accepting and rejecting states" becomes `Stmt.mapHalt`: replace
   every `halt` leaf with `write flip halt`.  Because only `goto` and `halt`
   consume steps in TM1, the complement machine halts at *exactly* the same
   step with the flipped verdict — complement is free.

## Relation to existing work

* Mathlib PR [#33132](https://github.com/leanprover-community/mathlib4/pull/33132)
  (single-tape `FinTM0` complexity, `EvalsToInTime`) is complementary: a
  different machine model with relational timing.  A bridge between the two
  is natural follow-up work.
* `Mathlib/Computability/TuringMachine/Computable.lean` defines
  `TM2ComputableInPolyTime` for functions; this file provides the *language
  class* layer that was missing.

## Provenance note

Developed and verified in an offline sandbox: mathlib sources reconstructed
file-for-file from the `v4.30.0` tag (via jsDelivr CDN pinned to commit
`c5ea0035…`), dependency repositories obtained as git archives with authentic
SHAs from Software Heritage, compiled artifacts from mathlib's official Azure
cache. None of this affects verification: the kernel checks the proofs
locally, and the standard workflow above reproduces the build from canonical
sources.
