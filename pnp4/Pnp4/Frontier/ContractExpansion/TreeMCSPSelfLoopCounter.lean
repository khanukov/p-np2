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

end ContractExpansion
end Frontier
end Pnp4
