import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroRoute

/-!
# `bZeroRouteProgram` run-through, P1 region (NP-verifier track — D2t-3 routing run-through)

The composed routing program `bZeroRouteProgram := seq gammaSelfLoopScan stepRightThenBranch` runs the
scan in `seq`'s **first region** (phases `0..1`, which run `gammaSelfLoopScan`'s transitions directly),
then hands off into `stepRightThenBranch`.  This module lifts the scan's behaviour through the `seq`
P1-region simulation (`runConfig_seq_succ_P1_normal_*`): replicating `gammaSelfLoopScan`'s scanning loop
inside `seq`.

* `bZeroRouteProgram_P1_scanning` — while the leading cells are `0`, the scan stays in phase `0`,
  advancing the head one cell per step, tape unchanged (the back-edge loop, in `seq`'s P1 region).

`seq`'s P1-accept (phase `1`) is where the handoff fires (`runConfig_seq_succ_P1_boundary`), landing in
`stepRightThenBranch` (phase `2`) = the input to the P2-region run-through
(`bZeroRouteProgram_P2_runConfig_branch_*`).  The terminator step (reaching phase `1` at the first `1`),
the handoff, and gluing P1 + handoff + P2 via `runConfig_add` are the next steps (then `ε`/`ζ`).

The per-step `gammaSelfLoopScan.transition` values are evaluated by the isolated helpers below — keeping
`simp [gammaSelfLoopScan]` out of the `seq` `runConfig` goal (where it would also unfold the machine and
break the layout hypotheses' matching).

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- `gammaSelfLoopScan` writes the scanned bit back (the write field is the input bit in every branch). -/
private theorem gscan_trans_write (i : Fin gammaSelfLoopScan.numPhases) (s : Unit) (b : Bool) :
    (gammaSelfLoopScan.transition i s b).snd.snd.fst = b := by
  simp only [gammaSelfLoopScan]; split <;> [split; skip] <;> rfl

/-- In the scan phase (`i.val = 0`) reading a `0`, `gammaSelfLoopScan` stays in phase `0`. -/
private theorem gscan_trans_phase0 (i : Fin gammaSelfLoopScan.numPhases) (s : Unit) (h : i.val = 0) :
    (gammaSelfLoopScan.transition i s false).fst.val = 0 := by
  simp [gammaSelfLoopScan, h]

/-- In the scan phase (`i.val = 0`) reading a `0`, `gammaSelfLoopScan` moves right. -/
private theorem gscan_trans_move0 (i : Fin gammaSelfLoopScan.numPhases) (s : Unit) (h : i.val = 0) :
    (gammaSelfLoopScan.transition i s false).snd.snd.snd = Move.right := by
  simp [gammaSelfLoopScan, h]

/-- Scan back-edge loop inside `seq`'s P1 region: if the first `z` cells are `0` (and `z` is within the
tape), then for every `k ≤ z` running `k` steps from the start leaves the program in phase `0` with the
head advanced to `k` and the tape unchanged. -/
theorem bZeroRouteProgram_P1_scanning {L : Nat} (x : Boolcube.Point L) (z : Nat)
    (hz : z < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) < z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = false) :
    ∀ k, k ≤ z →
      (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).tape
          = ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hbit : (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).tape
          (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).head = false := by
        rw [htp]; exact hzeros _ (by rw [hhd]; omega)
      have h1 : (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).state).fst : Nat)
          < gammaSelfLoopScan.numPhases := by rw [hph]; decide
      have hne : (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).state).fst : Nat)
          ≠ gammaSelfLoopScan.acceptPhase.val := by rw [hph]; decide
      have hbnd : ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).head : Nat) + 1
          < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [runConfig_seq_succ_P1_normal_phase gammaSelfLoopScan stepRightThenBranch
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k h1 hne, hbit]
        exact gscan_trans_phase0 _ _ hph
      · rw [runConfig_seq_succ_P1_normal_head gammaSelfLoopScan stepRightThenBranch
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k h1 hne, hbit,
          gscan_trans_move0 _ _ hph]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [runConfig_seq_succ_P1_normal_tape gammaSelfLoopScan stepRightThenBranch
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k h1 hne, hbit,
          gscan_trans_write]
        have hself : (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
            ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).write
            (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
            ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).head false
            = (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
            ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).tape := by
          funext j
          by_cases hj : j = (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
              ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) k).head
          · subst hj; simp [Configuration.write, hbit]
          · simp [Configuration.write, hj]
        rw [hself, htp]

/-- In the scan phase (`i.val = 0`) reading a `1`, `gammaSelfLoopScan` jumps to its done phase (`1`). -/
private theorem gscan_trans_phase1 (i : Fin gammaSelfLoopScan.numPhases) (s : Unit) (h : i.val = 0) :
    (gammaSelfLoopScan.transition i s true).fst.val = 1 := by
  simp [gammaSelfLoopScan, h]

/-- In the scan phase (`i.val = 0`) reading a `1`, `gammaSelfLoopScan` stays put (rests on the marker). -/
private theorem gscan_trans_movestay (i : Fin gammaSelfLoopScan.numPhases) (s : Unit) (h : i.val = 0) :
    (gammaSelfLoopScan.transition i s true).snd.snd.snd = Move.stay := by
  simp [gammaSelfLoopScan, h]

/-- Terminator step inside `seq`'s P1 region: with the first `z` cells `0` and cell `z` a `1`, after
`z + 1` steps the scan rests in phase `1` (`gammaSelfLoopScan`'s accept = `seq`'s P1-accept), head on the
marker (`= z`), tape unchanged.  Applies `bZeroRouteProgram_P1_scanning` at `k = z`, then one terminator
step (reading the `1` → phase `1`, stay).  Phase `1` is where `runConfig_seq_succ_P1_boundary` then hands
off into `stepRightThenBranch` (phase `2`). -/
theorem bZeroRouteProgram_P1_runConfig_terminator {L : Nat} (x : Boolcube.Point L) (z : Nat)
    (hz : z < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) < z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = false)
    (hterm : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) = z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = true) :
    (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1)).head : Nat) = z
      ∧ (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1)).tape
          = ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape := by
  obtain ⟨hph, hhd, htp⟩ := bZeroRouteProgram_P1_scanning x z hz hzeros z (le_refl z)
  have hbit : (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z).tape
      (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z).head = true := by
    rw [htp]; exact hterm _ hhd
  have h1 : (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z).state).fst : Nat)
      < gammaSelfLoopScan.numPhases := by rw [hph]; decide
  have hne : (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z).state).fst : Nat)
      ≠ gammaSelfLoopScan.acceptPhase.val := by rw [hph]; decide
  refine ⟨?_, ?_, ?_⟩
  · rw [runConfig_seq_succ_P1_normal_phase gammaSelfLoopScan stepRightThenBranch
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z h1 hne, hbit]
    exact gscan_trans_phase1 _ _ hph
  · rw [runConfig_seq_succ_P1_normal_head gammaSelfLoopScan stepRightThenBranch
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z h1 hne, hbit,
      gscan_trans_movestay _ _ hph]
    simp only [Configuration.moveHead]
    exact hhd
  · rw [runConfig_seq_succ_P1_normal_tape gammaSelfLoopScan stepRightThenBranch
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z h1 hne, hbit,
      gscan_trans_write]
    have hself : (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z).write
        (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z).head true
        = (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z).tape := by
      funext j
      by_cases hj : j = (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) z).head
      · subst hj; simp [Configuration.write, hbit]
      · simp [Configuration.write, hj]
    rw [hself, htp]

end ContractExpansion
end Frontier
end Pnp4
