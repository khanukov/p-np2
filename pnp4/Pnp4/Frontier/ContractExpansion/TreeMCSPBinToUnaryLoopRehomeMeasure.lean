import Complexity.TMVerifier.TuringToolkit.BinaryCounter
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehomeBodyRun
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryMeasure

/-!
# `binToUnaryLoopRehome` one-pass measure decrease (NP-verifier track — D2t-3 `ε`)

`hstep`'s measure ingredient.  The body run-through `binToUnaryLoopRehome_body_runConfig_onePass` returns
its post-tape explicitly: `B`'s low block `[head+1, head+1+j)` flips `0 → 1`, its lowest set bit
`head+1+j` flips `1 → 0` (a borrow), and `U` gains one `1` at `head−u−1`.  This module reads the **net
arithmetic effect** off that post-tape — the borrow drops `counterValue B` by exactly one — directly on
the loop machine `binToUnaryLoopRehome` (offset `+15`, phase `15`).

This is the strict measure decrease `loopUntilSink_reachesSink`'s `hstep` consumes (with `μ :=
counterValue B`).  It mirrors the standalone `binToUnaryBody_onePass_counterValue`
(`TreeMCSPBinToUnaryMeasure.lean`): the post-tape matches `counterValue_first_zero_diff`'s hypotheses with
`c := after`, `c' := c0`, `start := head+1`; `U`'s new bit at `head−u−1 < head+1` sits strictly left of
the `counterValue` window `[head+1, head+1+w)`, so it leaves the counter value untouched.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-- **One-pass measure-decrease (loop machine).**  From a HOME config at the body-start phase `15` with
`B > 0` (lowest set bit at `head+1+j`) and `U = 1^u` to the left, one body pass drops the little-endian
counter value of the width-`w` block `[head+1, head+1+w)` by exactly one:
`counterValue (after) + 1 = counterValue (before)`.  The strict measure decrease for
`loopUntilSink_reachesSink`'s `hstep` with `μ := counterValue B`.  Hypotheses match
`binToUnaryLoopRehome_body_runConfig_onePass`; `w` (with `j < w`) is the counter window's width. -/
theorem binToUnaryLoopRehome_body_onePass_counterValue {L : Nat}
    (c0 : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) (hphase : (c0.state.fst : Nat) = 15)
    (j : Nat) (hj : (c0.head : Nat) + 1 + j < binToUnaryLoopRehome.toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 + j → c0.tape p = true)
    (h_sentinel : c0.tape c0.head = false) (hHOME : 0 < (c0.head : Nat))
    (u : Nat) (hUfit : u + 1 ≤ (c0.head : Nat))
    (hU : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (c0.head : Nat) - u ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) → c0.tape p = true)
    (hUboundary : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - u - 1 → c0.tape p = false)
    (w : Nat) (hjw : j < w)
    (hwfit : (c0.head : Nat) + 1 + w ≤ binToUnaryLoopRehome.toPhased.toTM.tapeLength L) :
    counterValue (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (onePassSteps j u))
          ((c0.head : Nat) + 1) w + 1
      = counterValue c0 ((c0.head : Nat) + 1) w := by
  unfold onePassSteps
  obtain ⟨_, _, hTape⟩ :=
    binToUnaryLoopRehome_body_runConfig_onePass c0 hphase j hj h_zeros h_one h_sentinel hHOME u hUfit hU
      hUboundary
  set cF := TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0
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
    exact h_one ⟨(c0.head : Nat) + 1 + j, hb⟩ rfl
  · -- beyond `j`, the counter cells are untouched by the pass.
    intro i hij hiw hb
    rw [hTape ⟨(c0.head : Nat) + 1 + i, hb⟩,
      if_neg (by show ¬((c0.head : Nat) + 1 + i = (c0.head : Nat) - u - 1); omega),
      if_neg (by show ¬((c0.head : Nat) + 1 ≤ (c0.head : Nat) + 1 + i
        ∧ (c0.head : Nat) + 1 + i < (c0.head : Nat) + 1 + j); omega),
      if_neg (by show ¬((c0.head : Nat) + 1 + i = (c0.head : Nat) + 1 + j); omega)]

end ContractExpansion
end Frontier
end Pnp4
