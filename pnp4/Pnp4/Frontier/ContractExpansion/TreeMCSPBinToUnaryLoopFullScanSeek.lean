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

/-- **Seek scan step (phase `w+10`, read `0`)** = `selfLoopScanLeft` re-entry: scan one cell left, phase
stays `w + 10`; tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_scan0 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 10)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 10
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat)
          = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 10 < 2) := by omega
  have hge2 : ¬ (w + 8 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hbit, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hbit, hge, hge2]
    rw [hmove]
    have hne0 : ¬ (c.head : Nat) = 0 := by omega
    simp [Configuration.moveHead, hne0]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hbit, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write, hbit]
    · simp [Configuration.write, hj]

/-- **Seek scan step (phase `w+10`, read `1`)** = `selfLoopScanLeft` stop on `U`'s seed: phase `w + 11`;
head/tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_scan1 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 10)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 11
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 10 < 2) := by omega
  have hge2 : ¬ (w + 8 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hbit, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hbit, hge, hge2]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hbit, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write, hbit]
    · simp [Configuration.write, hj]

/-- **Leftward scanning invariant.**  From `c0` at composition phase `w + 10`, if the `k` cells
`(c0.head - k, c0.head]` are all `0` (and `k ≤ c0.head`), then after `k` steps the loop is still at
phase `w + 10`, the head has moved left to `c0.head - k`, and the tape is unchanged. -/
theorem binToUnaryLoopFullScan_seek_scanLeft_run (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = w + 10) :
    ∀ k : Nat, k ≤ (c0.head : Nat) →
      (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
        (c0.head : Nat) - k < (q : Nat) → (q : Nat) ≤ (c0.head : Nat) → c0.tape q = false) →
      (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).state).fst : Nat) = w + 10
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨by simpa using hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun q hq1 hq2 => h0 q (by omega) hq2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 k with hc
      have hhd' : (c.head : Nat) = (c0.head : Nat) - k := hhd
      have hheadpos : 0 < (c.head : Nat) := by rw [hhd']; omega
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd']; omega) (by rw [hhd']; omega)
      have hiph : (c.state.fst : Nat) = w + 10 := hph
      obtain ⟨sp, sh, st⟩ := binToUnaryLoopFullScan_seek_scan0 w c
        (i := c.state.fst) (s := c.state.snd) hiph rfl hbit hheadpos
      refine ⟨sp, ?_, ?_⟩
      · rw [sh, hhd']; omega
      · rw [st, htp]

/-- **Seek step (phase `w+11`)** = `selfLoopScanLeft` → `stepRightOnce` handoff: phase `w + 12`;
head/tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_w11 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 11)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 12
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 11 < 2) := by omega
  have hge2 : ¬ (w + 9 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Seek step (phase `w+12`)** = the final `stepRightOnce` move onto the sentinel: head `+1`,
phase `w + 13`. -/
theorem binToUnaryLoopFullScan_seek_w12 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 12)
    (hstate : c.state = ⟨i, s⟩)
    (hbound : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 13
      ∧ ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat)
          = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 12 < 2) := by omega
  have hge2 : ¬ (w + 10 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbound]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Seek step (phase `w+13`)** = final `stepRightOnce` → seek-idle handoff: phase `w + 14`;
head/tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_w13 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 13)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 14
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 13 < 2) := by omega
  have hge2 : ¬ (w + 11 < w + 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Seek step (phase `w+14`)** = seek-idle → `binToUnaryBody` handoff: phase `w + 15` (body start);
head/tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_w14 (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} (hi : (i : Nat) = w + 14)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = w + 15
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hge : ¬ (w + 14 < 2) := by omega
  have hge2 : ¬ (w + 12 < w + 2) := by omega
  have hbs : (binToUnaryBody.startPhase : Nat) = 0 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
      bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2, hbs]
    omega
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
    have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2, hbs]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    have hb : ((binToUnaryLoopBodyFullScan w).transition i () (c.tape c.head)).2.2.1 = c.tape c.head := by
      simp [binToUnaryLoopBodyFullScan, seq, seqList, seekHomeAfterRoute, bZeroFullScanRouteBody,
        bZeroFullScan, stepRightOnce, stepLeftOnce, selfLoopScanLeft, hi, hge, hge2, hbs]
    rw [hb]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Seek home run-through (composition) -/

/-- A helper: from a config at composition phase `w + 6`, run a single loop step and read off the result
of the named seek single-step. -/
private theorem stepHead_eq {w : Nat} {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (n : Nat) :
    TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (n + 1)
      = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM)
          (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c n) := by
  rw [TM.runConfig_succ]

/-- **Seek home run-through.**  From the seek start (composition phase `w + 6`, head `home + 2 + j` with
the sentinel at `home ≥ 1`), where `B`'s window + sentinel `[home, home + j]` are all `0` and `U`'s seed
`home - 1` is `1`, the loop re-homes: after `j + 10` steps it reaches the body start (composition phase
`w + 15`) with the head back at the sentinel `home` and the tape unchanged. -/
theorem binToUnaryLoopFullScan_seek_home (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L) (home j : Nat)
    (hphase : (c.state.fst : Nat) = w + 6) (hhome : 1 ≤ home)
    (hhead : (c.head : Nat) = home + 2 + j)
    (hb : home + 2 + j + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L)
    (hzeros : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      home ≤ (q : Nat) → (q : Nat) ≤ home + j → c.tape q = false)
    (hseed : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (q : Nat) = home - 1 → c.tape q = true) :
    (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (j + 10)).state).fst : Nat)
      = w + 15
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (j + 10)).head : Nat) = home
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (j + 10)).tape = c.tape := by
  -- step w6 (head home+2+j -> home+1+j)
  obtain ⟨p6, h6, t6⟩ := binToUnaryLoopFullScan_seek_w6 w c hphase rfl (by rw [hhead]; omega)
  set c1 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 1 with hc1
  have e1 : c1 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c := stepHead_eq c 0
  -- step w7
  obtain ⟨p7, h7, t7⟩ := binToUnaryLoopFullScan_seek_w7 w c1
    (i := c1.state.fst) (s := c1.state.snd) (by rw [e1]; exact p6) rfl
  set c2 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 2 with hc2
  have e2 : c2 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c1 := by
    rw [hc2, show (2:Nat) = 1+1 from rfl, TM.runConfig_succ, hc1]
  -- step w8 (head home+1+j -> home+j)
  have hh1 : (c1.head : Nat) = home + 1 + j := by rw [e1, h6, hhead]; omega
  obtain ⟨p8, h8, t8⟩ := binToUnaryLoopFullScan_seek_w8 w c2
    (i := c2.state.fst) (s := c2.state.snd) (by rw [e2]; exact p7) rfl
    (by rw [e2, h7, hh1]; omega)
  set c3 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 3 with hc3
  have e3 : c3 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c2 := by
    rw [hc3, show (3:Nat) = 2+1 from rfl, TM.runConfig_succ, hc2]
  -- step w9
  have hh2 : (c2.head : Nat) = home + 1 + j := by rw [e2, h7, hh1]
  obtain ⟨p9, h9, t9⟩ := binToUnaryLoopFullScan_seek_w9 w c3
    (i := c3.state.fst) (s := c3.state.snd) (by rw [e3]; exact p8) rfl
  set c4 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c 4 with hc4
  have e4 : c4 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c3 := by
    rw [hc4, show (4:Nat) = 3+1 from rfl, TM.runConfig_succ, hc3]
  have hh3 : (c3.head : Nat) = home + j := by rw [e3, h8, hh2]; omega
  have p4 : (c4.state.fst : Nat) = w + 10 := by rw [e4, p9]
  have hh4 : (c4.head : Nat) = home + j := by rw [e4, h9, hh3]
  have t4 : c4.tape = c.tape := by rw [e4, t9, e3, t8, e2, t7, e1, t6]
  -- scanLeft over [home, home+j] (j+1 zeros): head home+j -> home-1, phase stays w+10
  have hzeros4 : ∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
      (c4.head : Nat) - (j + 1) < (q : Nat) → (q : Nat) ≤ (c4.head : Nat) → c4.tape q = false := by
    intro q hq1 hq2; rw [t4]; rw [hh4] at hq1 hq2; exact hzeros q (by omega) (by omega)
  obtain ⟨ps, hs, ts⟩ := binToUnaryLoopFullScan_seek_scanLeft_run w c4 p4 (j + 1)
    (by rw [hh4]; omega) hzeros4
  set c5 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c4 (j + 1) with hc5
  have hh5 : (c5.head : Nat) = home - 1 := by rw [hs, hh4]; omega
  have t5 : c5.tape = c.tape := by rw [ts, t4]
  -- scan1 at the U-seed (home-1): phase w+11, head stays
  have hbit5 : c5.tape c5.head = true := by rw [t5]; exact hseed c5.head (by rw [hh5])
  obtain ⟨q1, k1, u1⟩ := binToUnaryLoopFullScan_seek_scan1 w c5
    (i := c5.state.fst) (s := c5.state.snd) ps rfl hbit5
  -- assemble: c (j+10) = stepConfig (c5 stepped once) then steps w11..w14
  set c6 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (4 + (j + 1) + 1) with hc6
  have e6 : c6 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c5 := by
    rw [hc6, TM.runConfig_succ, hc5, hc4, ← TM.runConfig_add]
  have p6' : (c6.state.fst : Nat) = w + 11 := by rw [e6]; exact q1
  have hh6 : (c6.head : Nat) = home - 1 := by rw [e6, k1, hh5]
  have t6' : c6.tape = c.tape := by rw [e6, u1, t5]
  obtain ⟨pa, ka, ua⟩ := binToUnaryLoopFullScan_seek_w11 w c6
    (i := c6.state.fst) (s := c6.state.snd) p6' rfl
  set c7 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (4 + (j + 1) + 1 + 1) with hc7
  have e7 : c7 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c6 := by
    rw [hc7, show (4+(j+1)+1+1 : Nat) = (4+(j+1)+1)+1 from rfl, TM.runConfig_succ, hc6]
  have p7' : (c7.state.fst : Nat) = w + 12 := by rw [e7]; exact pa
  have hh7 : (c7.head : Nat) = home - 1 := by rw [e7, ka, hh6]
  have t7' : c7.tape = c.tape := by rw [e7, ua, t6']
  obtain ⟨pb, kb, ub⟩ := binToUnaryLoopFullScan_seek_w12 w c7
    (i := c7.state.fst) (s := c7.state.snd) p7' rfl (by rw [hh7]; omega)
  set c8 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (4 + (j + 1) + 1 + 1 + 1) with hc8
  have e8 : c8 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c7 := by
    rw [hc8, show (4+(j+1)+1+1+1 : Nat) = (4+(j+1)+1+1)+1 from rfl, TM.runConfig_succ, hc7]
  have p8' : (c8.state.fst : Nat) = w + 13 := by rw [e8]; exact pb
  have hh8 : (c8.head : Nat) = home := by rw [e8, kb, hh7]; omega
  have t8' : c8.tape = c.tape := by rw [e8, ub, t7']
  obtain ⟨pc, kc, uc⟩ := binToUnaryLoopFullScan_seek_w13 w c8
    (i := c8.state.fst) (s := c8.state.snd) p8' rfl
  set c9 := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (4 + (j + 1) + 1 + 1 + 1 + 1) with hc9
  have e9 : c9 = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c8 := by
    rw [hc9, show (4+(j+1)+1+1+1+1 : Nat) = (4+(j+1)+1+1+1)+1 from rfl, TM.runConfig_succ, hc8]
  have p9' : (c9.state.fst : Nat) = w + 14 := by rw [e9]; exact pc
  have hh9 : (c9.head : Nat) = home := by rw [e9, kc, hh8]
  have t9' : c9.tape = c.tape := by rw [e9, uc, t8']
  obtain ⟨pd, kd, ud⟩ := binToUnaryLoopFullScan_seek_w14 w c9
    (i := c9.state.fst) (s := c9.state.snd) p9' rfl
  have hfin : TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c (j + 10)
      = TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c9 := by
    rw [hc9, show (j + 10 : Nat) = (4 + (j + 1) + 1 + 1 + 1 + 1) + 1 from by omega, TM.runConfig_succ]
  rw [hfin]
  refine ⟨pd, ?_, ?_⟩
  · rw [kd, hh9]
  · rw [ud, t9']

end ContractExpansion
end Frontier
end Pnp4
