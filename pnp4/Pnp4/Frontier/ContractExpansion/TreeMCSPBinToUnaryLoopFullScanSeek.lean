import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanStep2
import Pnp4.Frontier.ContractExpansion.TreeMCSPSeekHomeAfterRoute

/-!
# `binToUnaryLoopFullScan` — the seek-HOME run on the loop machine (NP-verifier track — D2t-3 `ε`, `hstep`)

After the post-divert connector reaches the seek start (phase `w + 6`, head `HOME+2+j`),
`seekHomeAfterRoute` re-homes the head to the sentinel `HOME`: two leftward steps (`HOME+2+j → HOME+j`),
a leftward self-loop scan over `B`'s `0`-run + the sentinel down to `U`'s seed `1` (`HOME-1`), then one
rightward step onto `HOME`.  Each loop step peels `loopUntilSink` and evaluates the four `seq` layers +
`seekHomeAfterRoute`'s `seqList`.

This brick ships the **single-step lemmas** of the seek region; the leftward scanning invariant and the
home run-through are the follow-up.

**Progress classification (AGENTS.md): Infrastructure** — standard triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Seek step (phase `w+6`)** = `seekHomeAfterRoute`'s first `stepLeftOnce` move: step one cell left,
reaching phase `w + 7`; tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_w6 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 6)
    (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 7
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat)
          = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 6 < 2) := by omega
  have hge2 : ¬ (w + 4 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    rw [hmove]
    have hne0 : ¬ (c.head : Nat) = 0 := by omega
    simp [Configuration.moveHead, hne0]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Seek step (phase `w+7`)** = first→second `stepLeftOnce` handoff: phase `w + 8`; head/tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_w7 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 7)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 8
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 7 < 2) := by omega
  have hge2 : ¬ (w + 5 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Seek step (phase `w+8`)** = second `stepLeftOnce` move: step one cell left, phase `w + 9`. -/
theorem binToUnaryLoopFullScan_seek_w8 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 8)
    (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 9
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat)
          = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 8 < 2) := by omega
  have hge2 : ¬ (w + 6 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    rw [hmove]
    have hne0 : ¬ (c.head : Nat) = 0 := by omega
    simp [Configuration.moveHead, hne0]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Seek step (phase `w+9`)** = second `stepLeftOnce` → `selfLoopScanLeft` handoff: phase `w + 10`;
head/tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_w9 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 9)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 10
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 9 < 2) := by omega
  have hge2 : ¬ (w + 7 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, hi, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
