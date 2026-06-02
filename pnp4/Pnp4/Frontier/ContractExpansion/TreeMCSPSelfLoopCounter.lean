import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Self-loop binary increment (NP-verifier track, brick 0 — variable-width counter machinery)

The verifier's loops (notably the `2^m`-row loop) iterate a data-dependent number of times and so need
a **variable-width** counter on the tape — but the toolkit's `incrementProgram k` is fixed-`k`, and a
single fixed verifier `M` cannot pick `k` per input (see `TM_VERIFIER_STRATEGY.md` §6's correction).
The fix is the same back-edge idea proven for the gamma scan: a **self-loop** binary increment.

`selfLoopIncrement` adds `1` to a little-endian counter starting at the head (LSB first, carry toward
the right/MSB).  Phase `0` is the *carry* phase: while it reads a `1` it writes a `0` and advances
(the carry propagates), re-entering itself (the back-edge); on reading a `0` it writes a `1` and stops
(phase `1`).  This stops at the first `0` **regardless of the counter's width**, so it has a fixed
2-phase structure yet operates on a data-dependent-width counter — exactly what `M` requires.

This module builds the program and its structural facts (`timeBound`, never-moves-left, single-step
lemmas).  The semantic correctness (`counterValue` increases by one, with overflow handling) reuses
the toolkit's `counterValue` and is the next brick.  This builds no verifier and proves no separation.
-/

/-- Self-loop binary increment of a little-endian tape counter at the head.  Carry phase `0`
re-enters itself (writing `0`, advancing) while reading `1`; on reading `0` it writes `1` and stops
(phase `1`).  Fixed 2-phase structure, variable-width operation. -/
def selfLoopIncrement : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨0, by omega⟩, (), false, Move.right)
      else (⟨1, by omega⟩, (), true, Move.stay)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopIncrement_timeBound (n : Nat) :
    selfLoopIncrement.timeBound n = n := rfl

/-- The increment never moves the head left: the carry advances right, otherwise stays. -/
theorem selfLoopIncrement_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopIncrement.transition i s b).2.2.2 ≠ Move.left := by
  unfold selfLoopIncrement
  dsimp only
  split_ifs <;> simp

/-- The compiled increment TM never moves its head left (lifts the transition fact through
`toPhased`/`toTM`; composes via `seqList_neverMovesLeft`). -/
theorem selfLoopIncrement_neverMovesLeft :
    TMNeverMovesLeft (selfLoopIncrement.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact selfLoopIncrement_transition_move i s b

/-! ### Single-step lemmas

The carry step (phase `0` reading `1`): write `0`, advance right, stay in phase `0` (the back-edge).
The stop step (phase `0` reading `0`): write `1`, stay, go to the done phase `1`. -/

/-- Carry step (phase `0`, bit `1`): the phase stays `0` (the self-loop re-entry). -/
theorem selfLoopIncrement_stepConfig_carry_phase {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Carry step (phase `0`, bit `1`): the head advances right (carry propagates). -/
theorem selfLoopIncrement_stepConfig_carry_head {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Carry step (phase `0`, bit `1`): the read `1` is flipped to `0` at the head. -/
theorem selfLoopIncrement_stepConfig_carry_tape {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).tape = c.write c.head false := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Stop step (phase `0`, bit `0`): the phase becomes the done phase `1`. -/
theorem selfLoopIncrement_stepConfig_stop_phase {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Stop step (phase `0`, bit `0`): the head stays put. -/
theorem selfLoopIncrement_stepConfig_stop_head {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit, Configuration.moveHead]

/-- Stop step (phase `0`, bit `0`): the read `0` is flipped to `1` at the head. -/
theorem selfLoopIncrement_stepConfig_stop_tape {L : Nat}
    (c : Configuration (M := selfLoopIncrement.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopIncrement.toPhased.toTM) c).tape = c.write c.head true := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopIncrement, hi, hbit]

/-- Carry-ripple invariant (structural backbone of the increment): if the first `k` counter cells are
all `1`, then after `k ≤ L` steps from the initial configuration the carry is still propagating —
phase `0`, head at `k`, and the tape has exactly cells `[0, k)` flipped to `0` (the rest unchanged).
Proved by induction with the carry single-step lemmas; the back-edge fires because every read so far
was a `1`.  This tracks the *evolving* tape (unlike the tape-preserving gamma scan), and is the step
toward the `counterValue + 1` correctness. -/
theorem selfLoopIncrement_runConfig_carry {L : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ L →
      (∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
        (p : Nat) < k →
        (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p = true) →
      (((TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
          (selfLoopIncrement.toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
          (selfLoopIncrement.toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ ∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
            (selfLoopIncrement.toPhased.toTM.initialConfig x) k).tape p
            = (if (p : Nat) < k then false
                else (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p) := by
  intro k
  induction k with
  | zero =>
      intro _ _
      refine ⟨rfl, rfl, ?_⟩
      intro p; simp
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp => h1 p (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
        (selfLoopIncrement.toPhased.toTM.initialConfig x) k with hc
      have hbnd : (c.head : Nat) + 1 < selfLoopIncrement.toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + L + 1; omega
      have hbit : c.tape c.head = true := by
        rw [htp]
        have hlt : ¬ (c.head : Nat) < k := by rw [hhd]; omega
        rw [if_neg hlt]
        exact h1 c.head (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopIncrement_stepConfig_carry_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopIncrement_stepConfig_carry_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopIncrement_stepConfig_carry_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self,
            if_pos (show (c.head : Nat) < k + 1 by rw [hhd]; omega)]
        · rw [Configuration.write_other c hp false, htp p]
          have hpc : (p : Nat) ≠ k := fun h => hp (Fin.ext (by rw [hhd]; exact h))
          split_ifs <;> first | rfl | (exfalso; omega)

/-- After-increment configuration: if the first `j` counter cells are `1` and cell `j` is `0`
(`j ≤ L`), then after `j + 1` steps the increment is done — phase `1`, head on cell `j`, and the tape
has cells `[0, j)` cleared to `0`, cell `j` set to `1`, and everything beyond unchanged.  Combines
the carry-ripple invariant at `j` with one terminating "stop" step (the read `0` is flipped to `1`).
This is the increment's result configuration, feeding the `counterValue + 1` correctness. -/
theorem selfLoopIncrement_runConfig_stop {L : Nat} (x : Boolcube.Point L) (j : Nat) (hj : j ≤ L)
    (h_ones : ∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p = true)
    (h_zero : ∀ hb : j < selfLoopIncrement.toPhased.toTM.tapeLength L,
      (selfLoopIncrement.toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = false) :
    (((TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
        (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
          (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ ∀ p : Fin (selfLoopIncrement.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
            (selfLoopIncrement.toPhased.toTM.initialConfig x) (j + 1)).tape p
            = (if (p : Nat) < j then false
                else if (p : Nat) = j then true
                else (selfLoopIncrement.toPhased.toTM.initialConfig x).tape p) := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopIncrement_runConfig_carry x j hj h_ones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopIncrement.toPhased.toTM)
    (selfLoopIncrement.toPhased.toTM.initialConfig x) j with hc
  have hhead_eq : c.head = ⟨j, by rw [← hhd]; exact c.head.isLt⟩ := Fin.ext hhd
  have hbit : c.tape c.head = false := by
    rw [htp, if_neg (show ¬ (c.head : Nat) < j by rw [hhd]; omega), hhead_eq]
    exact h_zero _
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopIncrement_stepConfig_stop_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopIncrement_stepConfig_stop_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [selfLoopIncrement_stepConfig_stop_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self]
      simp [hhd]
    · rw [Configuration.write_other c hp true, htp p]
      have hpc : (p : Nat) ≠ j := fun h => hp (by rw [hhead_eq]; exact Fin.ext h)
      split_ifs <;> rfl

end ContractExpansion
end Frontier
end Pnp4
