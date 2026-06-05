import Pnp4.Frontier.ContractExpansion.TreeMCSPBZeroRouteRunP1

/-!
# `bZeroRouteProgram` run-through, final compose (NP-verifier track — D2t-3 routing run-through)

Glues the run-through together: after the handoff (`bZeroRouteProgram_P1_runConfig_handoff`, phase `2`,
head on the marker `z`, tape unchanged), two P2-region steps — driven on `seq` directly via
`runConfig_seq_succ_P2_*` and the `stepRightThenBranch` transition helpers below — read the discriminator
cell `z + 1` and land in the composed branch target:

* `bZeroRouteProgram_runConfig_decide_true` — discriminator `= 1` ⇒ after `z + 4` steps, phase `4`
  (`B = 0` → sink);
* `bZeroRouteProgram_runConfig_decide_false` — discriminator `= 0` ⇒ phase `5` (`B > 0` → body-entry).

The shared first P2 step (handoff → phase `3`, head `z + 1`, tape unchanged) is factored into the private
`bZeroRouteProgram_runConfig_step1`; the two branch theorems differ only in the second step's read bit and
branch lemma.  This completes the composed routing run-through (P1 region + handoff + P2 region, all on
the one `bZeroRouteProgram`).  The remaining D2t-3 pieces are `ε` (`loopUntilSink`) and `ζ`
(`|U| = value(B)`).

The `stepRightThenBranch.transition` field values are evaluated by isolated helpers (same discipline as
the `gscan_*` helpers), keeping `simp [stepRightThenBranch]` out of the `seq` `runConfig` goal.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- `stepRightThenBranch` writes the scanned bit back (the write field is the input bit in every
branch). -/
private theorem srb_trans_write (i : Fin stepRightThenBranch.numPhases) (s : Unit) (b : Bool) :
    (stepRightThenBranch.transition i s b).snd.snd.fst = b := by
  simp only [stepRightThenBranch]; split <;> [skip; split] <;> simp

/-- Phase `0` of `stepRightThenBranch` advances to phase `1`. -/
private theorem srb_trans_p0_phase (i : Fin stepRightThenBranch.numPhases) (s : Unit) (b : Bool)
    (h : i.val = 0) : (stepRightThenBranch.transition i s b).fst.val = 1 := by
  simp [stepRightThenBranch, h]

/-- Phase `0` of `stepRightThenBranch` moves right. -/
private theorem srb_trans_p0_move (i : Fin stepRightThenBranch.numPhases) (s : Unit) (b : Bool)
    (h : i.val = 0) : (stepRightThenBranch.transition i s b).snd.snd.snd = Move.right := by
  simp [stepRightThenBranch, h]

/-- Phase `1` of `stepRightThenBranch` reading `1` branches to phase `2`. -/
private theorem srb_trans_p1_phase_true (i : Fin stepRightThenBranch.numPhases) (s : Unit)
    (h : i.val = 1) : (stepRightThenBranch.transition i s true).fst.val = 2 := by
  simp [stepRightThenBranch, h]

/-- Phase `1` of `stepRightThenBranch` reading `0` branches to phase `3`. -/
private theorem srb_trans_p1_phase_false (i : Fin stepRightThenBranch.numPhases) (s : Unit)
    (h : i.val = 1) : (stepRightThenBranch.transition i s false).fst.val = 3 := by
  simp [stepRightThenBranch, h]

/-- Shared first P2 step: from the handoff (phase `2`, head `z`, tape unchanged) one step (step right)
reaches phase `3`, head `z + 1`, tape unchanged — the common prefix of both branch run-throughs. -/
private theorem bZeroRouteProgram_runConfig_step1 {L : Nat} (x : Boolcube.Point L) (z : Nat)
    (hz1 : z + 1 < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) < z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = false)
    (hterm : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) = z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = true) :
    (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).head : Nat) = z + 1
      ∧ (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).tape
          = ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape := by
  obtain ⟨hph_h, hhd_h, htp_h⟩ := bZeroRouteProgram_P1_runConfig_handoff x z (by omega) hzeros hterm
  have h2a : gammaSelfLoopScan.numPhases ≤ ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).state).fst.val := by
    rw [hph_h]; decide
  have hlt_a : ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).state).fst.val
      - gammaSelfLoopScan.numPhases < stepRightThenBranch.numPhases := by rw [hph_h]; decide
  have hi0 : ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).state).fst.val
      - gammaSelfLoopScan.numPhases = 0 := by rw [hph_h]; decide
  have hbnd_a : ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).head : Nat) + 1
      < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L := by rw [hhd_h]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [runConfig_seq_succ_P2_phase gammaSelfLoopScan stepRightThenBranch
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1) h2a hlt_a,
      srb_trans_p0_phase _ _ _ hi0]
    decide
  · rw [runConfig_seq_succ_P2_head gammaSelfLoopScan stepRightThenBranch
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1) h2a hlt_a,
      srb_trans_p0_move _ _ _ hi0]
    simp only [Configuration.moveHead, dif_pos hbnd_a]
    rw [hhd_h]
  · rw [runConfig_seq_succ_P2_tape gammaSelfLoopScan stepRightThenBranch
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1) h2a hlt_a,
      srb_trans_write]
    have hself : (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).write
        (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).head
        ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).tape
          (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).head)
        = (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).tape := by
      funext j; by_cases hj : j = (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
          ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1)).head
      · subst hj; simp [Configuration.write]
      · simp [Configuration.write, hj]
    rw [hself, htp_h]

/-- **Full run-through, `B = 0` branch.**  Layout: cells `[0, z)` are `0`, cell `z` is the scan-stop `1`,
and the discriminator cell `z + 1` is `1`.  Then `bZeroRouteProgram` runs: scan to `z` (`z + 1` steps,
phase `1`), handoff (phase `2`), step right (phase `3`, head `z + 1`), read the discriminator `1` (phase
`4`).  After `z + 1 + 1 + 1 + 1` steps it rests in composed phase `4` — the `B = 0` → sink target. -/
theorem bZeroRouteProgram_runConfig_decide_true {L : Nat} (x : Boolcube.Point L) (z : Nat)
    (hz1 : z + 1 < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) < z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = false)
    (hterm : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) = z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = true)
    (hdisc : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) = z + 1 →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = true) :
    (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x)
        (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 4 := by
  obtain ⟨hph1, hhd1, htp1⟩ := bZeroRouteProgram_runConfig_step1 x z hz1 hzeros hterm
  have h2b : gammaSelfLoopScan.numPhases ≤ ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).state).fst.val := by
    rw [hph1]; decide
  have hlt_b : ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).state).fst.val
      - gammaSelfLoopScan.numPhases < stepRightThenBranch.numPhases := by rw [hph1]; decide
  have hi1 : ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).state).fst.val
      - gammaSelfLoopScan.numPhases = 1 := by rw [hph1]; decide
  have hread : (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).tape
      (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).head = true := by
    rw [htp1]; exact hdisc _ hhd1
  rw [runConfig_seq_succ_P2_phase gammaSelfLoopScan stepRightThenBranch
    ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1) h2b hlt_b,
    hread, srb_trans_p1_phase_true _ _ hi1]
  decide

/-- **Full run-through, `B > 0` branch.**  Layout: cells `[0, z)` are `0`, cell `z` is the scan-stop `1`
(the lowest set bit), and the discriminator cell `z + 1` is a `0` separator.  Then `bZeroRouteProgram`
runs: scan to `z`, handoff, step right, read the separator `0` → composed phase `5` (the `B > 0` →
body-entry target), after `z + 1 + 1 + 1 + 1` steps. -/
theorem bZeroRouteProgram_runConfig_decide_false {L : Nat} (x : Boolcube.Point L) (z : Nat)
    (hz1 : z + 1 < (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) < z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = false)
    (hterm : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) = z →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = true)
    (hdisc : ∀ p : Fin ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.tapeLength L),
      (p : Nat) = z + 1 →
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x).tape p = false) :
    (((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
        ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x)
        (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 5 := by
  obtain ⟨hph1, hhd1, htp1⟩ := bZeroRouteProgram_runConfig_step1 x z hz1 hzeros hterm
  have h2b : gammaSelfLoopScan.numPhases ≤ ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).state).fst.val := by
    rw [hph1]; decide
  have hlt_b : ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).state).fst.val
      - gammaSelfLoopScan.numPhases < stepRightThenBranch.numPhases := by rw [hph1]; decide
  have hi1 : ((TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).state).fst.val
      - gammaSelfLoopScan.numPhases = 1 := by rw [hph1]; decide
  have hread : (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).tape
      (TM.runConfig (M := (seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM)
      ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1)).head = false := by
    rw [htp1]; exact hdisc _ hhd1
  rw [runConfig_seq_succ_P2_phase gammaSelfLoopScan stepRightThenBranch
    ((seq gammaSelfLoopScan stepRightThenBranch).toPhased.toTM.initialConfig x) (z + 1 + 1 + 1) h2b hlt_b,
    hread, srb_trans_p1_phase_false _ _ hi1]
  decide

end ContractExpansion
end Frontier
end Pnp4
