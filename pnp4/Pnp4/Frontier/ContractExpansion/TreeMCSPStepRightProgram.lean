import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Single-step rightward move (NP-verifier track — D2 transcoder, D2t-3c building block)

`stepRightOnce` is the trivial one-cell **rightward** move: a fixed 2-phase program that, in phase `0`,
writes the scanned bit back, moves the head **right** by one — clamping at the tape's right end, i.e. at
head `tapeLength − 1` the head stays put (`Move.right` semantics), so its run lemma
`stepRightOnce_runConfig_one` guards with `head + 1 < tapeLength`; the boundary case is the explicit
`stepRightOnce_stepConfig_head_clamp` — and halts (phase `1`).

It is the deterministic mirror of `stepLeftOnce`.  The binary→unary loop body (D2t-3c-γ) uses it to step
**off** the `0`-sentinel (HOME) onto `B`'s low cell before `selfLoopDecrement` — a single deterministic
right step that a bit-conditional scan self-loop (which would stop on the sentinel's `0`) cannot provide.

This ships the program and its one-step run-behaviour, with the standalone and `seqP2` (non-first phase)
lifts.  Builds no verifier and proves no separation; all surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple.  **No `P ≠ NP` claim.**
-/

/-- Single rightward step: phase `0` writes the scanned bit back, moves right (clamping at the tape's
right end — at head `tapeLength − 1` it stays), and halts (phase `1`). -/
def stepRightOnce : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.right)
    else (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun _ => 1

@[simp] theorem stepRightOnce_timeBound (n : Nat) : stepRightOnce.timeBound n = 1 := rfl

@[simp] theorem stepRightOnce_numPhases : stepRightOnce.numPhases = 2 := rfl

@[simp] theorem stepRightOnce_startPhase_val : (stepRightOnce.startPhase : Nat) = 0 := rfl

@[simp] theorem stepRightOnce_acceptPhase_val : (stepRightOnce.acceptPhase : Nat) = 1 := rfl

/-- The single rightward step never moves the head left (it moves right while active, otherwise stays). -/
theorem stepRightOnce_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (stepRightOnce.transition i s b).2.2.2 ≠ Move.left := by
  unfold stepRightOnce
  dsimp only
  split_ifs <;> simp

/-- Phase-`0` step: the phase advances to the done phase `1`. -/
theorem stepRightOnce_stepConfig_phase {L : Nat}
    (c : Configuration (M := stepRightOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, stepRightOnce, hi]

/-- Phase-`0` step: the head moves right by one (when not at the right end). -/
theorem stepRightOnce_stepConfig_head {L : Nat}
    (c : Configuration (M := stepRightOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hhead : (c.head : Nat) + 1 < stepRightOnce.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  have hmove : (TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightOnce, hi]
  rw [hmove, Configuration.moveHead_right_lt c hhead]

/-- Boundary clamp: a phase-`0` step at the right end (`head + 1 = tapeLength`) leaves the head put
(`Move.right` clamps) — the explicit witness that "moves right by one" holds only inside the tape. -/
theorem stepRightOnce_stepConfig_head_clamp {L : Nat}
    (c : Configuration (M := stepRightOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hhead : ¬ ((c.head : Nat) + 1 < stepRightOnce.toPhased.toTM.tapeLength L)) :
    (TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).head = c.head := by
  have hmove : (TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightOnce, hi]
  rw [hmove, Configuration.moveHead_right_clamp c hhead]

/-- Phase-`0` step: the tape is unchanged (the scanned bit is written back). -/
theorem stepRightOnce_stepConfig_tape {L : Nat}
    (c : Configuration (M := stepRightOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightOnce, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One-step run behaviour: from phase `0` with the head not at the right end, after one step the program
is in the done phase `1`, the head has moved one cell right, and the tape is unchanged. -/
theorem stepRightOnce_runConfig_one {L : Nat}
    (c : Configuration (M := stepRightOnce.toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hhead : (c.head : Nat) + 1 < stepRightOnce.toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := stepRightOnce.toPhased.toTM) c 1).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := stepRightOnce.toPhased.toTM) c 1).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.runConfig (M := stepRightOnce.toPhased.toTM) c 1).tape = c.tape := by
  rw [runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact stepRightOnce_stepConfig_phase c (i := c.state.fst) (s := c.state.snd) hphase rfl
  · exact stepRightOnce_stepConfig_head c (i := c.state.fst) (s := c.state.snd) hphase rfl hhead
  · exact stepRightOnce_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) hphase rfl

/-- Done-phase (`1`) idle: a step from phase `1` preserves phase, head, and tape. -/
theorem stepRightOnce_stepConfig_done {L : Nat}
    (c : Configuration (M := stepRightOnce.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).state).fst.val = 1
    ∧ (TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).head = c.head
    ∧ (TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightOnce, hi]
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightOnce, hi, Configuration.moveHead]
  · have hwrite : (TM.stepConfig (M := stepRightOnce.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
      unfold TM.stepConfig
      rw [hstate]
      simp only [PhasedProgram.toTM_step]
      simp [ConstStatePhasedProgram.toPhased, stepRightOnce, hi]
    rw [hwrite]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Composition lift: the single right step as a non-first phase (`seqP2`)

So `stepRightOnce` composes as a phase of `seq P1 stepRightOnce` (phase offset `P1.numPhases`) — used in
the binary→unary loop body to step from HOME onto the counter before the decrement. -/

/-- The single right step as a non-first phase: advance to the shifted done phase `P1.numPhases + 1`. -/
theorem stepRightOnce_seqP2_stepConfig_phase (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 stepRightOnce).toPhased.toTM) L)
    {i : Fin (seq P1 stepRightOnce).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq P1 stepRightOnce).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 stepRightOnce c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [stepRightOnce, hsub]

/-- The single right step as a non-first phase: the head moves right by one (when not at the right end). -/
theorem stepRightOnce_seqP2_stepConfig_head (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 stepRightOnce).toPhased.toTM) L)
    {i : Fin (seq P1 stepRightOnce).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩)
    (hhead : (c.head : Nat) + 1 < (seq P1 stepRightOnce).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (seq P1 stepRightOnce).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hmove : (TM.stepConfig (M := (seq P1 stepRightOnce).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
    rw [seq_stepConfig_P2_head P1 stepRightOnce c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [stepRightOnce, hsub]
  rw [hmove, Configuration.moveHead_right_lt c hhead]

/-- The single right step as a non-first phase: the tape is unchanged (scanned bit written back). -/
theorem stepRightOnce_seqP2_stepConfig_tape (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 stepRightOnce).toPhased.toTM) L)
    {i : Fin (seq P1 stepRightOnce).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq P1 stepRightOnce).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 stepRightOnce).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P2_tape P1 stepRightOnce c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [stepRightOnce, hsub]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One-step run behaviour as a non-first phase: from phase `P1.numPhases` with the head inside the tape,
after one step the phase is `P1.numPhases + 1`, the head has moved one cell right, and the tape is
unchanged. -/
theorem stepRightOnce_seqP2_runConfig_one (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq P1 stepRightOnce).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = P1.numPhases)
    (hhead : (c.head : Nat) + 1 < (seq P1 stepRightOnce).toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := (seq P1 stepRightOnce).toPhased.toTM) c 1).state).fst : Nat)
        = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 stepRightOnce).toPhased.toTM) c 1).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.runConfig (M := (seq P1 stepRightOnce).toPhased.toTM) c 1).tape = c.tape := by
  rw [runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact stepRightOnce_seqP2_stepConfig_phase P1 c (i := c.state.fst) (s := c.state.snd) hphase rfl
  · exact stepRightOnce_seqP2_stepConfig_head P1 c (i := c.state.fst) (s := c.state.snd) hphase rfl hhead
  · exact stepRightOnce_seqP2_stepConfig_tape P1 c (i := c.state.fst) (s := c.state.snd) hphase rfl

end ContractExpansion
end Frontier
end Pnp4
