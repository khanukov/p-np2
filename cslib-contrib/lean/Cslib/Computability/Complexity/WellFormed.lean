/-
Copyright (c) 2026 Dmitry Khanukov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Khanukov
-/

module

public import Cslib.Computability.Complexity.Defs

/-!
# Input well-formedness checking for pair-alphabet deciders

> **DRAFT — not yet compiled.** This file is part of the PR-3 toolkit draft for the
> complexity-class development. Every referenced library identifier has been checked against
> the CSLib/Mathlib sources, but the proofs have not been elaborated by Lean. The two
> correctness lemmas of `checkComputer` are stated as **named open TODOs** (see the final
> section), not as `sorry`ed theorems: nothing in this file claims more than it proves.

A verifier for `NP` is a decider over the pair alphabet `Symbol ⊕ Bool`. The `P ⊆ NP`
construction runs a decider for `L : Language Symbol` inside a decider for a pair language,
so it must first check that its input word uses only symbols of the form
`Sum.inl _` — on any other input the simulated decider's behavior is unspecified, and a
total decider must nevertheless produce a verdict. `checkComputer` is that scanner:

* on an input of the form `inputWord (x.map Sum.inl)` it halts with the tape unchanged,
  in at most `2 * x.length + 2` steps;
* on any other input word over `DecSym (Symbol ⊕ Bool)` of the form `inputWord w` it
  halts with the tape holding exactly the error marker `[errSym Symbol]`, in at most
  `2 * w.length + 2` steps.

The error marker `errSym Symbol = DecSym.input (Sum.inr false)` is chosen to be *outside
the range* of the alphabet injection used by the `P ⊆ NP` relabeling
(`Cslib.Computability.Complexity.liftSym`), so the machine downstream of the checker halts
in place on the error path (`relabelComputer_outputsWithinTime_of_lower_eq_none`) rather
than running on garbage.

## Main definitions

* `CheckState`: the four control states of the scanner.
* `checkComputer Symbol : SingleTapeTM (DecSym (Symbol ⊕ Bool))`: the scanner itself.
* `errSym Symbol`: the error marker.
* `CheckComputerSpec Symbol`: the correctness specification of the scanner, as a
  `Prop`-valued structure. The `P ⊆ NP` assembly
  (`Cslib.Computability.Complexity.P_subset_NP_of_checkComputerSpec`) is proven from this
  specification alone; discharging it is the named TODO below.

## Main results

* `checkComputer_outputsWithinTime_nil`, `checkComputer_outputsWithinTime_inr`:
  fully proven sanity anchors — an explicit good-path run (the empty input) and an explicit
  error-path run (a single ill-formed symbol), each computed step by step. These certify
  that the transition table does what the specification says on the smallest instances of
  both paths.
* `StackTape.cons_none_nil`, `StackTape.cons_head?_mapSome_tail`, … : the small normal-form
  lemmas about `StackTape` on which the full correctness proof (and any future
  "reject ill-formed inputs" machine) rests. They are proven here, in the same PR that
  needs them.

## The machine

`checkComputer` sweeps right over the input; while it sees only symbols
`DecSym.input (Sum.inl _)` it stays in state `scan`, otherwise it switches to `errFwd` and
keeps sweeping (without writing) to the first blank. It then returns left:

* good path (`back`): sweep left over the word without changing it; on the blank one cell
  left of the word, step right and halt. The head ends on the leftmost input cell, so the
  halting configuration is exactly `haltCfg (inputWord w)`.
* error path (`errBack`): sweep left *erasing* every cell; on the blank one cell left of
  the word, write the error marker and halt in place, so the halting configuration is
  exactly `haltCfg [errSym Symbol]`.

Termination of the leftward sweeps is structural, not sensed: the machine turns around
exactly once, and on the way left every cell it can encounter before the left end is a
`some` cell, so the first `none` it reads *is* the left end. The tape representation makes
the erased suffix literally disappear (`StackTape.cons_none_nil`), which is why the halting
configurations above are on-the-nose equalities of configurations, not equalities up to
padding.
-/

@[expose] public section

open Relation

namespace Cslib

namespace Turing.StackTape

/-! ### Normal-form helpers for `StackTape`

These are the stack-level facts the correctness proof of `checkComputer` reduces to.
Candidates for upstreaming into `Cslib.Foundations.Data.StackTape`.
-/

variable {A : Type*}

/-- Pushing a blank onto the empty stack is a no-op: trailing blanks do not exist.
This is the normalization fact that makes the erasing sweep of `checkComputer` end in
*exactly* the halting configuration `haltCfg [errSym Symbol]`. -/
@[simp]
theorem cons_none_nil : cons none (nil : StackTape A) = nil :=
  toList_injective (by simp)

@[simp]
theorem mapSome_nil : mapSome ([] : List A) = nil := rfl

theorem mapSome_cons (a : A) (l : List A) :
    mapSome (a :: l) = cons (some a) (mapSome l) :=
  toList_injective (by simp [mapSome])

/-- The head entry of a rendered word is the head of the word: `some a` for a word
starting with `a`, and the blank `none` for the empty word. -/
@[simp]
theorem head_mapSome (l : List A) : (mapSome l).head = l.head? := by
  cases l <;> rfl

@[simp]
theorem tail_mapSome (l : List A) : (mapSome l).tail = mapSome l.tail := by
  cases l <;> rfl

/-- Splitting off the head cell of a rendered word and pushing it back is the identity.
This is the single stack identity behind the sweeps of `checkComputer`: moving the head
one cell along a rendered word regroups the tape by exactly this equation. -/
theorem cons_head?_mapSome_tail (l : List A) :
    cons l.head? (mapSome l.tail) = mapSome l := by
  cases l with
  | nil => simp
  | cons a t => simp [mapSome_cons]

end Turing.StackTape

namespace Computability.Complexity

open Cslib.Turing Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Fintype Symbol]

/-- The control states of `checkComputer`. -/
inductive CheckState : Type where
  /-- Sweeping right; all symbols so far are well-formed. -/
  | scan
  /-- Sweeping left on the good path, back to the start of the word. -/
  | back
  /-- Sweeping right after detecting an ill-formed symbol. -/
  | errFwd
  /-- Sweeping left on the error path, erasing the word. -/
  | errBack
deriving DecidableEq

instance : Fintype CheckState where
  elems := {.scan, .back, .errFwd, .errBack}
  complete x := by cases x <;> decide

/-- The error marker of `checkComputer`. It is a pair-alphabet *input* symbol (not a
verdict), chosen from the certificate side so that it is outside the range of the alphabet
injection `liftSym` of the `P ⊆ NP` relabeling: the machine downstream of the checker
halts in place when it sees it. -/
def errSym (Symbol : Type) : DecSym (Symbol ⊕ Bool) :=
  .input (Sum.inr false)

/--
The input well-formedness scanner over the pair alphabet: decide whether every tape
symbol has the form `DecSym.input (Sum.inl _)`. If so, halt with the tape unchanged
(and the head back on the leftmost cell); otherwise erase the tape and halt with output
exactly `[errSym Symbol]`. Both paths take at most `2 * n + 2` steps on an `n`-cell input.
-/
def checkComputer (Symbol : Type) [Fintype Symbol] :
    SingleTapeTM (DecSym (Symbol ⊕ Bool)) where
  State := CheckState
  q₀ := .scan
  tr q s :=
    match q, s with
    -- good symbol: keep it, move right, keep scanning
    | .scan, some (.input (.inl _)) => ⟨⟨s, some .right⟩, some .scan⟩
    -- ill-formed symbol: keep it for now, move right, remember the error
    | .scan, some _ => ⟨⟨s, some .right⟩, some .errFwd⟩
    -- blank after a well-formed word: turn around
    | .scan, none => ⟨⟨none, some .left⟩, some .back⟩
    -- return sweep, good path: change nothing
    | .back, some _ => ⟨⟨s, some .left⟩, some .back⟩
    -- blank left of the word: step right onto the first cell and halt
    | .back, none => ⟨⟨none, some .right⟩, none⟩
    -- error path, forward: change nothing until the blank
    | .errFwd, some _ => ⟨⟨s, some .right⟩, some .errFwd⟩
    -- blank after an ill-formed word: turn around
    | .errFwd, none => ⟨⟨none, some .left⟩, some .errBack⟩
    -- return sweep, error path: erase every cell
    | .errBack, some _ => ⟨⟨none, some .left⟩, some .errBack⟩
    -- blank left of the erased word: write the marker and halt in place
    | .errBack, none => ⟨⟨some (errSym Symbol), none⟩, none⟩

/-- Sanity anchor, good path: on the empty input, `checkComputer` halts after exactly two
steps (turn around on the initial blank, then step back right and halt) with the tape
still empty. This is `CheckComputerSpec.ok` at `x = []`, proven by explicit computation. -/
theorem checkComputer_outputsWithinTime_nil :
    (checkComputer Symbol).OutputsWithinTime
      ([] : List (DecSym (Symbol ⊕ Bool))) [] 2 := by
  have h1 : (checkComputer Symbol).TransitionRelation
      ((checkComputer Symbol).initCfg [])
      ⟨some CheckState.back, BiTape.nil⟩ := rfl
  have h2 : (checkComputer Symbol).TransitionRelation
      ⟨some CheckState.back, BiTape.nil⟩
      ((checkComputer Symbol).haltCfg []) := rfl
  exact RelatesWithinSteps.of_relatesInSteps
    (RelatesInSteps.head _ _ _ _ h1 (RelatesInSteps.single h2))

/-- Sanity anchor, error path: on the single ill-formed symbol `Sum.inr b`, `checkComputer`
halts after exactly four steps with output exactly the error marker. This is
`CheckComputerSpec.err` at `w = [Sum.inr b]` (with `4 = 2 * 1 + 2`), proven by explicit
computation; in particular it exercises the `StackTape.cons_none_nil` normalization that
ends the erasing sweep in an on-the-nose halting configuration. -/
theorem checkComputer_outputsWithinTime_inr (b : Bool) :
    (checkComputer Symbol).OutputsWithinTime
      (inputWord [Sum.inr b]) [errSym Symbol] 4 := by
  have h1 : (checkComputer Symbol).TransitionRelation
      ((checkComputer Symbol).initCfg (inputWord [Sum.inr b]))
      ⟨some CheckState.errFwd,
        ⟨none, StackTape.mapSome [DecSym.input (Sum.inr b)], StackTape.nil⟩⟩ := rfl
  have h2 : (checkComputer Symbol).TransitionRelation
      ⟨some CheckState.errFwd,
        ⟨none, StackTape.mapSome [DecSym.input (Sum.inr b)], StackTape.nil⟩⟩
      ⟨some CheckState.errBack,
        ⟨some (DecSym.input (Sum.inr b)), StackTape.nil, StackTape.nil⟩⟩ := rfl
  have h3 : (checkComputer Symbol).TransitionRelation
      ⟨some CheckState.errBack,
        ⟨some (DecSym.input (Sum.inr b)), StackTape.nil, StackTape.nil⟩⟩
      ⟨some CheckState.errBack, BiTape.nil⟩ := rfl
  have h4 : (checkComputer Symbol).TransitionRelation
      ⟨some CheckState.errBack, BiTape.nil⟩
      ((checkComputer Symbol).haltCfg [errSym Symbol]) := rfl
  exact RelatesWithinSteps.of_relatesInSteps
    (RelatesInSteps.head _ _ _ _ h1
      (RelatesInSteps.head _ _ _ _ h2
        (RelatesInSteps.head _ _ _ _ h3 (RelatesInSteps.single h4))))

/--
Correctness specification of `checkComputer`, as a `Prop`-valued structure:

* `ok`: on every well-formed input (a word of `Sum.inl` symbols rendered by `inputWord`),
  the scanner halts with the tape unchanged, within `2n + 2` steps;
* `err`: on every other input word, it halts with output exactly the error marker,
  within `2n + 2` steps.

The `P ⊆ NP` assembly (`P_subset_NP_of_checkComputerSpec`) consumes exactly this
specification. It is stated as a structure so that the assembly can be proven — and
reviewed — independently of the scanner's correctness proof, which is the one genuinely
long machine-analysis argument of the development (see the TODO below). No theorem in
this development asserts `CheckComputerSpec Symbol` before it is proven.
-/
structure CheckComputerSpec (Symbol : Type) [Fintype Symbol] : Prop where
  /-- Well-formed inputs pass through unchanged, in at most `2n + 2` steps. -/
  ok : ∀ x : List Symbol,
    (checkComputer Symbol).OutputsWithinTime
      (inputWord (x.map Sum.inl)) (inputWord (x.map Sum.inl)) (2 * x.length + 2)
  /-- Ill-formed inputs are erased to the error marker, in at most `2n + 2` steps. -/
  err : ∀ w : List (Symbol ⊕ Bool), (∀ x : List Symbol, w ≠ x.map Sum.inl) →
    (checkComputer Symbol).OutputsWithinTime
      (inputWord w) [errSym Symbol] (2 * w.length + 2)

/-!
## Open TODO (named): `checkComputer_spec`

TODO(checkComputer_spec): prove

```
theorem checkComputer_spec (Symbol : Type) [Fintype Symbol] : CheckComputerSpec Symbol
```

This is the single hard machine-construction proof of the `P ⊆ NP` development
(estimated 250–350 lines). It is an induction over the run with explicit configuration
invariants; the invariants are pinned down here so that the proof is mechanical:

With `W := inputWord w` (all cells `some`), `n := W.length`, define the mid-sweep tape

```
tapeAt (pre suf : List (DecSym (Symbol ⊕ Bool))) : BiTape (DecSym (Symbol ⊕ Bool)) :=
  ⟨suf.head?,                       -- head cell: first symbol of `suf`, blank at `suf = []`
   StackTape.mapSome pre.reverse,   -- cells left of the head, nearest first
   StackTape.mapSome suf.tail⟩      -- cells right of the head
```

(tape cells and `List.head?` both live in `Option`, so the head component is literally
`suf.head?`; cf. `StackTape.head_mapSome`). Then `tapeAt [] W = BiTape.mk₁ W`, and
`tapeAt W []` is the turnaround configuration at the blank one cell right of the word.
Four phase lemmas, each by induction on a list:

1. `scan_run` (induction on `suf`): if every symbol of `suf` is `.input (Sum.inl _)`, then
   `⟨some .scan, tapeAt pre suf⟩ →^[suf.length] ⟨some .scan, tapeAt (pre ++ suf) []⟩`.
   The step case regroups the tape by `StackTape.mapSome_cons`, `head_mapSome`,
   `tail_mapSome`, and `List.reverse_append`; the write is the identity
   (`BiTape.write` with the symbol already under the head).
2. `errFwd_run` (same induction, no well-formedness hypothesis):
   `⟨some .errFwd, tapeAt pre suf⟩ →^[suf.length] ⟨some .errFwd, tapeAt (pre ++ suf) []⟩`,
   plus one detection step from `.scan` at the first ill-formed symbol.
3. `back_run` (induction on `pre`): from the turnaround, sweep left to one cell *left of
   the word*:
   `⟨some .back, tapeAt pre suf⟩ →^[pre.length + 1]
      ⟨some .back, ⟨none, StackTape.nil, StackTape.mapSome (pre ++ suf)⟩⟩`
   (each left move regroups the right stack by `StackTape.cons_head?_mapSome_tail`; the
   left stack empties cell by cell). The final transition (`.back` on `none`) moves right
   onto the first cell of the word, regrouping once more by `cons_head?_mapSome_tail` into
   exactly `haltCfg W`.
4. `errBack_run` (induction on `pre`): starting from the turnaround
   `⟨some .errBack, ⟨(mapSome pre.reverse-style head), …, StackTape.nil⟩⟩`, each erasing
   step keeps the right stack `StackTape.nil` by `StackTape.cons_none_nil`, ending in
   `⟨some .errBack, BiTape.nil⟩`; the final transition writes the marker and halts in
   `haltCfg [errSym Symbol]` on the nose (this exact endgame is exercised by the proven
   `checkComputer_outputsWithinTime_inr`).

Step counts: good path `(n + 1) + n + 1 = 2n + 2`; error path
`(k + 1) + (n - 1 - k) + 1 + n + 1 = 2n + 2` where `k` is the position of the first
ill-formed symbol. The `err` hypothesis `∀ x, w ≠ x.map Sum.inl` yields such a `k` by
induction on `w` (a word over `Symbol ⊕ Bool` with no first `Sum.inr` symbol is a map of
`Sum.inl`s).

The helper lemmas these inductions need (`cons_none_nil`, `mapSome_cons`, `head_mapSome`,
`tail_mapSome`, `cons_head?_mapSome_tail`) are proven above, in this file, so the TODO is
self-contained machine analysis with no new infrastructure.
-/

end Computability.Complexity

end Cslib
