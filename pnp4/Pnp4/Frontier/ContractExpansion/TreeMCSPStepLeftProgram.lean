import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Single-step leftward move (NP-verifier track — D2 transcoder, D2t-3c building block)

`stepLeftOnce` is the trivial one-cell **leftward** move: a fixed 2-phase program that, in phase `0`,
writes the scanned bit back, moves the head **left** by one, and halts (phase `1`).  The binary→unary
loop's home-seek (D2t-3c-β) uses it to step **off** the decrement's cleared `0`-cell onto the flipped
`1`-block before `selfLoopScanLeftOne` scans that block back to the sentinel — a single deterministic
left step that a `scan`-style self-loop (which is bit-conditional) cannot provide.

This ships the program and its one-step run-behaviour.  Builds no verifier and proves no separation; all
surfaces carry only the standard `[propext, Classical.choice, Quot.sound]` triple.
-/

/-- Single leftward step: phase `0` writes the scanned bit back, moves left, and halts (phase `1`). -/
def stepLeftOnce : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.left)
    else (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun _ => 1

@[simp] theorem stepLeftOnce_timeBound (n : Nat) : stepLeftOnce.timeBound n = 1 := rfl
@[simp] theorem stepLeftOnce_numPhases : stepLeftOnce.numPhases = 2 := rfl
@[simp] theorem stepLeftOnce_startPhase_val : (stepLeftOnce.startPhase : Nat) = 0 := rfl
@[simp] theorem stepLeftOnce_acceptPhase_val : (stepLeftOnce.acceptPhase : Nat) = 1 := rfl

/-- The single left step never moves the head right (it moves left, then stays in the done phase). -/
theorem stepLeftOnce_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (stepLeftOnce.transition i s b).2.2.2 ≠ Move.right := by
  unfold stepLeftOnce
  dsimp only
  split_ifs <;> simp

/-! ### Single-step lemmas (phase `0`) -/

/-- Phase-`0` step: advance to the done phase `1`. -/
theorem stepLeftOnce_stepConfig_phase {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]

/-- Phase-`0` step: the head moves left by one (when not at the left end). -/
theorem stepLeftOnce_stepConfig_head {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1 := by
  have hmove : (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
  rw [hmove]
  have hne : ¬ (c.head : Nat) = 0 := by omega
  simp only [Configuration.moveHead, dif_neg hne]

/-- Phase-`0` step: the tape is unchanged (the scanned bit is written back). -/
theorem stepLeftOnce_stepConfig_tape {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One-step run behaviour: from phase `0` with the head not at the left end, after one step the program
is in the done phase `1`, the head has moved one cell left, and the tape is unchanged. -/
theorem stepLeftOnce_runConfig_one {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0) (hhead : 0 < (c.head : Nat)) :
    (((TM.runConfig (M := stepLeftOnce.toPhased.toTM) c 1).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := stepLeftOnce.toPhased.toTM) c 1).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.runConfig (M := stepLeftOnce.toPhased.toTM) c 1).tape = c.tape := by
  rw [TM.runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact stepLeftOnce_stepConfig_phase c (i := c.state.fst) (s := c.state.snd) hphase rfl
  · exact stepLeftOnce_stepConfig_head c (i := c.state.fst) (s := c.state.snd) hphase rfl hhead
  · exact stepLeftOnce_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) hphase rfl

/-- Done-phase (`1`) idle: a step from phase `1` preserves phase, head, and tape. -/
theorem stepLeftOnce_stepConfig_done {L : Nat}
    (c : Configuration (M := stepLeftOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).state).fst.val = 1
    ∧ (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).head = c.head
    ∧ (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi, Configuration.moveHead]
  · have hwrite : (TM.stepConfig (M := stepLeftOnce.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
      unfold TM.stepConfig
      rw [hstate]
      simp only [PhasedProgram.toTM_step]
      simp [ConstStatePhasedProgram.toPhased, stepLeftOnce, hi]
    rw [hwrite]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
