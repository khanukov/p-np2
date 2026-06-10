import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanBodyBridge

/-!
# `binToUnaryLoopFullScan` body single-steps (NP-verifier track — D2t-3 `ε`, `hstep` body leg)

The `binToUnaryBody` one-pass engine, re-derived **directly on the sound loop machine** at composition
offset `+ (w + 15)`, via the body bridge (`TreeMCSPBinToUnaryLoopFullScanBodyBridge.lean`): each step is
the loop peel (`binToUnaryLoopFullScan_transition_body`) + the bridge (collapse the depth-4 nesting to
`binToUnaryBody`'s local transition at phase `k`) + an evaluation of that concrete-phase transition.
This is the symbolic-`w` FullScan analogue of `TreeMCSPBinToUnaryLoopRehomeBodyStep.lean`.

Phase map (loop ↔ `binToUnaryBody` ↔ element): `w+15↔0` stepRight move, `w+16↔1` handoff, `w+17↔2`
decrement, `w+18↔3` handoff, `w+19↔4` stepLeft, `w+20↔5` handoff, `w+21↔6` scanLeft, `w+22↔7` handoff,
`w+23↔8` stepLeft, `w+24↔9` handoff, `w+25↔10` appendLeft, `w+26↔11` handoff, `w+27↔12` scanRight,
`w+28↔13` handoff (into the `idleCS` accept at `w+29 ↔ 14` = the loop body's accept / back-edge target).
The four scan work-phases (`w+17` decrement, `w+21` scanLeft, `w+25` appendLeft, `w+27` scanRight) are
bit-conditional, so each splits into a read-`1` and a read-`0` lemma.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 0 on the sound loop (composition phase `w + 15 + 0`). -/
theorem binToUnaryLoopFullScan_body_w15 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 0) (hstate : c.state = ⟨i, s⟩) (hbnd : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 1
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 0 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 0 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 0 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 1 on the sound loop (composition phase `w + 15 + 1`). -/
theorem binToUnaryLoopFullScan_body_w16 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 2
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 1 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 1 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 1 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 2 on the sound loop (composition phase `w + 15 + 2`). -/
theorem binToUnaryLoopFullScan_body_w17_one (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 2) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 3
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.write c.head false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 2 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 2 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = false := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 2 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hbw]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 2 on the sound loop (composition phase `w + 15 + 2`). -/
theorem binToUnaryLoopFullScan_body_w17_zero (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 2) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) (hbnd : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 2
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.write c.head true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 2 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 2 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = true := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 2 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hbw]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 3 on the sound loop (composition phase `w + 15 + 3`). -/
theorem binToUnaryLoopFullScan_body_w18 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 3) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 4
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 3 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 3 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 3 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 4 on the sound loop (composition phase `w + 15 + 4`). -/
theorem binToUnaryLoopFullScan_body_w19 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 4) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 5
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 4 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 4 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 4 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 5 on the sound loop (composition phase `w + 15 + 5`). -/
theorem binToUnaryLoopFullScan_body_w20 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 5) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 6
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 5 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 5 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 5 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 6 on the sound loop (composition phase `w + 15 + 6`). -/
theorem binToUnaryLoopFullScan_body_w21_one (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 6) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 6
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 6 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 6 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 6 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 6 on the sound loop (composition phase `w + 15 + 6`). -/
theorem binToUnaryLoopFullScan_body_w21_zero (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 6) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 7
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 6 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 6 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 6 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 7 on the sound loop (composition phase `w + 15 + 7`). -/
theorem binToUnaryLoopFullScan_body_w22 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 7) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 8
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 7 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 7 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 7 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 8 on the sound loop (composition phase `w + 15 + 8`). -/
theorem binToUnaryLoopFullScan_body_w23 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 8) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 9
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 8 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 8 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 8 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 9 on the sound loop (composition phase `w + 15 + 9`). -/
theorem binToUnaryLoopFullScan_body_w24 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 9) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 10
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 9 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 9 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 9 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 10 on the sound loop (composition phase `w + 15 + 10`). -/
theorem binToUnaryLoopFullScan_body_w25_one (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 10) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 10
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 10 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 10 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 10 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 10 on the sound loop (composition phase `w + 15 + 10`). -/
theorem binToUnaryLoopFullScan_body_w25_zero (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 10) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 11
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.write c.head true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 10 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 10 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = true := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 10 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hbw]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 11 on the sound loop (composition phase `w + 15 + 11`). -/
theorem binToUnaryLoopFullScan_body_w26 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 11) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 12
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 11 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 11 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 11 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 12 on the sound loop (composition phase `w + 15 + 12`). -/
theorem binToUnaryLoopFullScan_body_w27_one (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 12) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) (hbnd : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 12
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 12 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 12 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 12 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 12 on the sound loop (composition phase `w + 15 + 12`). -/
theorem binToUnaryLoopFullScan_body_w27_zero (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 12) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 13
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 12 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 12 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 12 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne, hbit]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- `binToUnaryBody` local phase 13 on the sound loop (composition phase `w + 15 + 13`). -/
theorem binToUnaryLoopFullScan_body_w28 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit}
    (hi : (i : Nat) = w + 15 + 13) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15 + 14
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
        binToUnaryLoopBodyFullScan_atBody_phase w 13 (by omega) hi () (c.tape c.head)]
    simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_move w 13 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate]
    have hbw : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head),
          binToUnaryLoopBodyFullScan_atBody_bit w 13 (by omega) hi () (c.tape c.head)]
      simp [binToUnaryBody, seqList, seq, stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, selfLoopAppendLeftOne, selfLoopScanRightOne]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
