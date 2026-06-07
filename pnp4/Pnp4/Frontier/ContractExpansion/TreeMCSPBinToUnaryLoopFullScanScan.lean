import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopFullScanPeel

/-!
# `binToUnaryLoopFullScan` — loop-machine scan run (NP-verifier track — D2t-3 `ε`, `hbase` core)

The `B = 0` scan on the loop machine: from composition phase `2` (the route-body start, after the
leading `stepRightOnce`), reading `0`s, advance phase-by-phase to phase `2 + w` (the sound test's `B = 0`
outcome = the `loopUntilSink` sink).  Each loop step peels `loopUntilSink` (`..._transition_body`, the
phase is `< w + 2 = sink < w + 29 = accept`) to the body, then evaluates the two `seq` layers + the scan.

**Progress classification (AGENTS.md): Infrastructure** — standard triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Loop scan step (read `0`), phase.**  At composition phase `2 + p` (`p < w`) reading `0`, advance to
`2 + p + 1`. -/
theorem binToUnaryLoopFullScan_stepConfig_scan_phase (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = 2 + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).state).fst.val = 2 + p + 1 := by
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  have hge : ¬ (2 + p < 2) := by omega
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (binToUnaryLoopFullScan w) c hstate,
      binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
  simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, hi, hbit, hp, hne, hlt2,
    hge, Nat.add_assoc]

/-- **Loop scan step (read `0`), head.**  Advance the head by one. -/
theorem binToUnaryLoopFullScan_stepConfig_scan_head (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = 2 + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false)
    (hbound : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).head : Nat)
      = (c.head : Nat) + 1 := by
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  have hge : ¬ (2 + p < 2) := by omega
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (binToUnaryLoopFullScan w) c hstate]
  have hmove : ((binToUnaryLoopFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, hi, hbit, hp, hne,
      hlt2, hge]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- **Loop scan step (read `0`), tape.**  The tape is unchanged. -/
theorem binToUnaryLoopFullScan_stepConfig_scan_tape (w : Nat) {L : Nat}
    (c : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    {i : Fin (binToUnaryLoopFullScan w).numPhases} {s : Unit} {p : Nat} (hp : p < w)
    (hi : (i : Nat) = 2 + p) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape = c.tape := by
  have hne : ¬ (p = w + 1) := by omega
  have hlt2 : p < w + 2 := by omega
  have hge : ¬ (2 + p < 2) := by omega
  have hwrite : (TM.stepConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [ConstStatePhasedProgram.toTM_stepConfig_tape (binToUnaryLoopFullScan w) c hstate,
        binToUnaryLoopFullScan_transition_body w (by omega) (by omega) s (c.tape c.head)]
    simp [binToUnaryLoopBodyFullScan, seq, bZeroFullScanRouteBody, bZeroFullScan, hi, hbit, hp, hne,
      hlt2, hge]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- **Loop scanning invariant.**  From `c0` at composition phase `2`, if the `j` cells from the head are
all `0` (`j ≤ w`, in bounds), then after `j` steps the loop's composition phase is `2 + j`, the head is at
`c0.head + j`, and the tape is unchanged. -/
theorem binToUnaryLoopFullScan_runConfig_scanning (w : Nat) {L : Nat}
    (c0 : Configuration (M := (binToUnaryLoopFullScan w).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 2) :
    ∀ j : Nat, j ≤ w →
      (c0.head : Nat) + j < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L →
      (∀ q : Fin ((binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (q : Nat) → (q : Nat) < (c0.head : Nat) + j → c0.tape q = false) →
      (((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 j).state).fst : Nat) = 2 + j
      ∧ ((TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _ _; exact ⟨by simpa using hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj hb h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun q hq1 hq2 => h0 q hq1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (binToUnaryLoopFullScan w).toPhased.toTM) c0 j with hc
      have hbnd : (c.head : Nat) + 1 < (binToUnaryLoopFullScan w).toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hpj : j < w := by omega
      have hiph : (c.state.fst : Nat) = 2 + j := hph
      refine ⟨?_, ?_, ?_⟩
      · rw [binToUnaryLoopFullScan_stepConfig_scan_phase w c
          (i := c.state.fst) (s := c.state.snd) hpj hiph rfl hbit]
        omega
      · rw [binToUnaryLoopFullScan_stepConfig_scan_head w c
          (i := c.state.fst) (s := c.state.snd) hpj hiph rfl hbit hbnd]
        omega
      · rw [binToUnaryLoopFullScan_stepConfig_scan_tape w c
          (i := c.state.fst) (s := c.state.snd) hpj hiph rfl hbit, htp]

end ContractExpansion
end Frontier
end Pnp4
