import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanScan

/-!
# `binToUnaryLoopFullScan` — the `B = 0 → sink` half of `ε` (NP-verifier track — D2t-3)

`loopUntilSink_reachesSink`'s `hbase` for the sound loop: from the loop start (phase `0`, head at the
sentinel `HOME`) with the counter `B` zero (`counterValue (HOME+1) w = 0`), the loop reaches the sink
(phase `w + 2`).  The run is the leading `stepRightOnce` (phase `0 → 2`, head `HOME → HOME+1`) followed
by the width-`w` full scan over all-`0` cells (phase `2 → 2 + w`); `δ1`
(`counterValue_eq_zero_imp_all_false`) turns the `counterValue = 0` hypothesis into the all-`0` window the
scan consumes.

**Progress classification (AGENTS.md): Infrastructure** — standard triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-- **Loop step (phase `0`)** = the leading `stepRightOnce`'s move: step one cell right, reaching phase
`1`; tape unchanged. -/
theorem binToUnaryLoopFullScan_step0 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = 0)
    (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = 1
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat)
          = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, stepRightOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, stepRightOnce, hi]
    rw [hmove]
    simp only [Configuration.moveHead, dif_pos hbound]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, stepRightOnce, hi]
    rw [this]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Loop step (phase `1`)** = the `stepRightOnce → bZeroFullScanRouteBody` handoff: jump to phase `2`
(the scan start); head and tape unchanged. -/
theorem binToUnaryLoopFullScan_step1 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = 1)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = 2
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, stepRightOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, stepRightOnce, hi]
    rw [hmove]
    simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, stepRightOnce, hi]
    rw [this]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **`B = 0` run-through (hbase).**  From the loop start (phase `0`, head `HOME`) with the width-`w`
counter window all-`0` (`counterValue (HOME+1) w = 0`), the loop reaches the sink phase `w + 2` after
`2 + w` steps. -/
theorem binToUnaryLoopFullScan_runConfig_hbase (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    (hstart : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + 1 + w < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (hzero : counterValue c0 ((c0.head : Nat) + 1) w = 0) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 (2 + w)).state).fst : Nat)
      = w + 2 := by
  -- step 0: the leading stepRightOnce move (head HOME → HOME+1)
  obtain ⟨h0p, h0h, h0t⟩ := binToUnaryLoopFullScan_step0 w c0 hstart rfl (by omega)
  -- step 1: the handoff to the scan start (phase 2)
  set c1 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 1 with hc1
  have hc1eq : c1 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 := by
    rw [hc1, show (1 : Nat) = 0 + 1 from rfl, TM.runConfig_succ]; rfl
  obtain ⟨h1p, h1h, h1t⟩ := binToUnaryLoopFullScan_step1 w c1
    (i := c1.state.fst) (s := c1.state.snd) (by rw [hc1eq]; exact h0p) rfl
  -- after 2 steps: phase 2, head HOME+1, tape unchanged
  set c2 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 2 with hc2
  have hc2eq : c2 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c1 := by
    rw [hc2, show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_succ, hc1]
  have h2p : (c2.state.fst : Nat) = 2 := by rw [hc2eq]; exact h1p
  have h2h : (c2.head : Nat) = (c0.head : Nat) + 1 := by
    rw [hc2eq, h1h, hc1eq, h0h]
  have h2t : c2.tape = c0.tape := by rw [hc2eq, h1t, hc1eq, h0t]
  -- the scan window [HOME+1, HOME+1+w) is all 0 (from counterValue = 0)
  have hzeros : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c2.head : Nat) ≤ (q : Nat) → (q : Nat) < (c2.head : Nat) + w → c2.tape q = false := by
    intro q hq1 hq2
    rw [h2t]
    have hqlt : (q : Nat) - ((c0.head : Nat) + 1) < w := by rw [h2h] at hq2; omega
    have hqge : (c0.head : Nat) + 1 ≤ (q : Nat) := by rw [h2h] at hq1; omega
    have := counterValue_eq_zero_imp_all_false c0 ((c0.head : Nat) + 1) w hzero
      ((q : Nat) - ((c0.head : Nat) + 1)) hqlt (by omega)
    simpa [Nat.add_sub_cancel' hqge] using this
  -- scan w zeros from phase 2 → phase 2 + w
  obtain ⟨hsp, _, _⟩ := binToUnaryLoopFullScan_runConfig_scanning w c2 h2p w (le_refl w)
    (by rw [h2h]; omega) hzeros
  rw [show (2 + w : Nat) = 2 + w from rfl, ← TM.runConfig_add, ← hc2] at *
  rw [hsp]; omega

end ContractExpansion
end Frontier
end Pnp4
