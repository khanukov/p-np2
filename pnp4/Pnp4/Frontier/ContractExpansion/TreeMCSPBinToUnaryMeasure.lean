import Complexity.TMVerifier.TuringToolkit.BinaryCounter
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryBody

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-!
# One-pass measure/output arithmetic (NP-verifier track — D2 transcoder, D2t-3c-ε ingredient)

`binToUnaryBody_runConfig_onePass` (the merged HOME→HOME engine) returns its post-tape explicitly: the
binary counter `B`'s low block `[head+1, head+1+j)` flips `0 → 1`, its lowest set bit `head+1+j` flips
`1 → 0` (a borrow), and the unary block `U` gains one `1` at `head-u-1`.  This module reads the **net
arithmetic effect** off that post-tape:

* `binToUnaryBody_onePass_counterValue` — the borrow drops `counterValue B` by exactly one.  This is
  the strict measure-decrease `loopUntilSink_reachesSink`'s `hstep` consumes (with measure
  `μ := counterValue B`) when wrapping `binToUnaryBody` into the conversion loop (D2t-3c-ε).
* `binToUnaryBody_onePass_appendedBit` — the produced `U`-bit at `head-u-1` is set, recording the
  `|U| + 1` growth (the output side, toward ζ's `|U| = value(B)`).

The counter step reuses the toolkit's `counterValue_first_zero_diff` (the bit-flip arithmetic of a
borrow): the post-tape matches its hypotheses with `c := after`, `c' := c0`, `start := head+1`.  `U`'s
new bit sits at `head-u-1 < head+1`, strictly left of the `counterValue` window `[head+1, head+1+w)`, so
it leaves the counter value untouched.

Builds no verifier and proves no separation; standard `[propext, Classical.choice, Quot.sound]` triple.
**No `P ≠ NP` claim.**
-/

/-- The one-pass `runConfig` step count — the argument `binToUnaryBody_runConfig_onePass` runs for
(the per-element step tally of the seven-element body).  Factored out so the statements below don't
repeat the literal; each proof `unfold`s it to the form the engine theorem returns. -/
abbrev onePassSteps (j u : Nat) : Nat :=
  2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1) + 1

/-- **One-pass measure-decrease.**  From HOME with `B > 0` (lowest set bit at `head+1+j`), one pass of
`binToUnaryBody` drops the little-endian counter value of the width-`w` block `[head+1, head+1+w)` by
exactly one: `counterValue (after) + 1 = counterValue (before)`.  This is the strict measure decrease
for `loopUntilSink_reachesSink`'s `hstep` with `μ := counterValue B`.  Hypotheses match
`binToUnaryBody_runConfig_onePass`; `w` (with `j < w`) is the counter window's width. -/
theorem binToUnaryBody_onePass_counterValue {L : Nat}
    (c0 : Configuration (M := bodyFull.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat)
    (hj : (c0.head : Nat) + 1 + j ≤ L)
    (hbnd : (c0.head : Nat) + 1 < bodyFull.toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ hb : (c0.head : Nat) + 1 + j < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + 1 + j, hb⟩ = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat))
    (u : Nat) (hUfit : u + 1 ≤ (c0.head : Nat))
    (hU : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) → c0.tape p = true)
    (hUboundary : ∀ hb : (c0.head : Nat) - u - 1 < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) - u - 1, hb⟩ = false)
    (w : Nat) (hjw : j < w)
    (hwfit : (c0.head : Nat) + 1 + w ≤ bodyFull.toPhased.toTM.tapeLength L) :
    counterValue (TM.runConfig (M := bodyFull.toPhased.toTM) c0 (onePassSteps j u))
          ((c0.head : Nat) + 1) w + 1
      = counterValue c0 ((c0.head : Nat) + 1) w := by
  unfold onePassSteps
  obtain ⟨_, _, hTape⟩ :=
    binToUnaryBody_runConfig_onePass c0 hphase j hj hbnd h_zeros h_one h_sentinel hHOME u hUfit hU
      hUboundary
  set cF := TM.runConfig (M := bodyFull.toPhased.toTM) c0
    (2 + (j + 1) + 1 + 1 + 1 + (j + 1) + 1 + 1 + 1 + (u + 1) + 1 + (u + 1 + 1) + 1)
  refine (counterValue_first_zero_diff cF c0 ((c0.head : Nat) + 1) j w hjw hwfit
    ?_ ?_ ?_ ?_ ?_).symm
  · -- after: low block `[head+1, head+1+j)` is all `1` (the borrow filled it in).
    intro i hi hb
    rw [hTape ⟨(c0.head : Nat) + 1 + i, hb⟩,
      if_neg (by show ¬((c0.head : Nat) + 1 + i = (c0.head : Nat) - u - 1); omega),
      if_pos (by show (c0.head : Nat) + 1 ≤ (c0.head : Nat) + 1 + i
        ∧ (c0.head : Nat) + 1 + i < (c0.head : Nat) + 1 + j; omega)]
  · -- after: the lowest set bit `head+1+j` was cleared to `0`.
    intro hb
    rw [hTape ⟨(c0.head : Nat) + 1 + j, hb⟩,
      if_neg (by show ¬((c0.head : Nat) + 1 + j = (c0.head : Nat) - u - 1); omega),
      if_neg (by show ¬((c0.head : Nat) + 1 ≤ (c0.head : Nat) + 1 + j
        ∧ (c0.head : Nat) + 1 + j < (c0.head : Nat) + 1 + j); omega),
      if_pos rfl]
  · -- before: low block was all `0` (input hypothesis `h_zeros`).
    intro i hi hb
    exact h_zeros ⟨(c0.head : Nat) + 1 + i, hb⟩
      (by show (c0.head : Nat) + 1 ≤ (c0.head : Nat) + 1 + i; omega)
      (by show (c0.head : Nat) + 1 + i < (c0.head : Nat) + 1 + j; omega)
  · -- before: the lowest set bit `head+1+j` was `1` (input hypothesis `h_one`).
    intro hb
    exact h_one hb
  · -- beyond `j`, the counter cells are untouched by the pass.
    intro i hij hiw hb
    rw [hTape ⟨(c0.head : Nat) + 1 + i, hb⟩,
      if_neg (by show ¬((c0.head : Nat) + 1 + i = (c0.head : Nat) - u - 1); omega),
      if_neg (by show ¬((c0.head : Nat) + 1 ≤ (c0.head : Nat) + 1 + i
        ∧ (c0.head : Nat) + 1 + i < (c0.head : Nat) + 1 + j); omega),
      if_neg (by show ¬((c0.head : Nat) + 1 + i = (c0.head : Nat) + 1 + j); omega)]

/-- **One-pass output bit.**  One pass sets the cell `head-u-1` (the new left end of the unary block
`U`) to `1`, recording the `|U| + 1` growth.  Read directly off `onePass`'s post-tape. -/
theorem binToUnaryBody_onePass_appendedBit {L : Nat}
    (c0 : Configuration (M := bodyFull.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat)
    (hj : (c0.head : Nat) + 1 + j ≤ L)
    (hbnd : (c0.head : Nat) + 1 < bodyFull.toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ hb : (c0.head : Nat) + 1 + j < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + 1 + j, hb⟩ = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat))
    (u : Nat) (hUfit : u + 1 ≤ (c0.head : Nat))
    (hU : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) → c0.tape p = true)
    (hUboundary : ∀ hb : (c0.head : Nat) - u - 1 < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) - u - 1, hb⟩ = false)
    (hb : (c0.head : Nat) - u - 1 < bodyFull.toPhased.toTM.tapeLength L) :
    (TM.runConfig (M := bodyFull.toPhased.toTM) c0 (onePassSteps j u)).tape
        ⟨(c0.head : Nat) - u - 1, hb⟩ = true := by
  unfold onePassSteps
  obtain ⟨_, _, hTape⟩ :=
    binToUnaryBody_runConfig_onePass c0 hphase j hj hbnd h_zeros h_one h_sentinel hHOME u hUfit hU
      hUboundary
  rw [hTape ⟨(c0.head : Nat) - u - 1, hb⟩, if_pos rfl]

end ContractExpansion
end Frontier
end Pnp4
