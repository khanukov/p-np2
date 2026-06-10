import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanPos

/-!
# `binToUnaryLoopFullScan` — the `B > 0` post-divert `stepRightOnce` connector (D2t-3 `ε`, `hstep`)

After the scan diverts on `B`'s lowest set bit (phase `w + 3`, head `HOME+1+j`), the loop body's second
`stepRightOnce` steps the head one cell right to `HOME+2+j` — the discriminator-style position the proven
`seekHomeAfterRoute` re-homes from — reaching the seek start (phase `w + 6`).  Three loop steps: the
route-body→stepRight handoff (`w+3 → w+4`), the rightward move (`w+4 → w+5`), and the
stepRight→seek handoff (`w+5 → w+6`).

**Progress classification (AGENTS.md): Infrastructure** — standard triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Loop handoff (phase `w+3 → w+4`)**: route-body accept hands off into the second `stepRightOnce`;
head and tape unchanged. -/
theorem binToUnaryLoopFullScan_step_w3 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 3)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 4
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 3 < 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Loop move (phase `w+4 → w+5`)**: the second `stepRightOnce`'s rightward move, head `+1`. -/
theorem binToUnaryLoopFullScan_step_w4 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 4)
    (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 5
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat)
          = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 4 < 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbound]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Loop handoff (phase `w+5 → w+6`)**: the second `stepRightOnce` hands off into `seekHomeAfterRoute`;
head and tape unchanged. -/
theorem binToUnaryLoopFullScan_step_w5 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 5)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 6
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 5 < 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, stepRightOnce, hi, hge]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **`B > 0` post-divert connector.**  From phase `w + 3` (head at the set bit `HOME+1+j`), after `3`
steps the loop reaches the seek start (phase `w + 6`) with the head one cell further right (`HOME+2+j`)
and the tape unchanged. -/
theorem binToUnaryLoopFullScan_runConfig_postDivert (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    (hstart : (c.state.fst : Nat) = w + 3)
    (hbound : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 3).state.fst : Nat) = w + 6
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 3).head : Nat)
          = (c.head : Nat) + 1
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 3).tape = c.tape := by
  obtain ⟨p0, h0, t0⟩ := binToUnaryLoopFullScan_step_w3 w c hstart rfl
  set c1 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 1 with hc1
  have hc1eq : c1 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c := by
    rw [hc1, show (1 : Nat) = 0 + 1 from rfl, TM.runConfig_succ]; rfl
  obtain ⟨p1, h1, t1⟩ := binToUnaryLoopFullScan_step_w4 w c1 (i := c1.state.fst) (s := c1.state.snd)
    (by rw [hc1eq]; exact p0) rfl (by rw [hc1eq, h0]; exact hbound)
  set c2 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 2 with hc2
  have hc2eq : c2 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c1 := by
    rw [hc2, show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_succ, hc1]
  obtain ⟨p2, h2, t2⟩ := binToUnaryLoopFullScan_step_w5 w c2 (i := c2.state.fst) (s := c2.state.snd)
    (by rw [hc2eq]; exact p1) rfl
  have hcompose : TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 3
      = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c2 := by
    rw [show (3 : Nat) = 2 + 1 from rfl, TM.runConfig_succ, hc2]
  rw [hcompose]
  refine ⟨p2, ?_, ?_⟩
  · rw [h2, hc2eq, h1, hc1eq, h0]
  · rw [t2, hc2eq, t1, hc1eq, t0]

end ContractExpansion
end Frontier
end Pnp4
