import Pnp4.Frontier.ContractExpansion.TreeMCSPSeekHomeAfterRoute

/-!
# `seekHomeAfterRoute` run-through — single-step lemmas (NP-verifier track — D2t-3 `ε`)

Per-step `stepConfig` lemmas for `seekHomeAfterRoute = seqList [stepLeftOnce, stepLeftOnce,
selfLoopScanLeft, stepRightOnce]`, built bottom-up before the scanning run-through (the toolkit's
single-step-first discipline).  Phase layout: `0` = first `stepLeftOnce` move, `1` = its handoff, `2` =
second `stepLeftOnce` move, `3` = handoff, `4` = `selfLoopScanLeft` scan, `5` = handoff, `6` =
`stepRightOnce` move, `7` = handoff, `8` = `idleCS` (accept).
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

-- The depth-navigation `simp` sets vary per phase/component; some carry a redundant unfold lemma.
-- This is a proof-engineering convenience, not a soundness concern; silence the style linter here.
set_option linter.unusedSimpArgs false

/-- `seekHomeAfterRoute` is `seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])` —
the shape the depth-1 `seq_stepConfig_P1_*` lemmas consume. -/
theorem seekHomeAfterRoute_eq_seq :
    seekHomeAfterRoute
      = seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) := rfl

/-- Step 1 (phase `0`, the first `stepLeftOnce`'s move): the phase advances to `1`.  Stated over the
`seq`-head form (defeq to `seekHomeAfterRoute` by `seekHomeAfterRoute_eq_seq`), so the depth-1
`seq_stepConfig` lemmas match syntactically. -/
theorem seekHomeAfterRoute_step1_phase {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 1 := by
  rw [seq_stepConfig_P1_normal_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])
      c (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [stepLeftOnce, hi]

/-- Step 1 (phase `0`): the head moves one cell left (when not at the left end). -/
theorem seekHomeAfterRoute_step1_head {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head : Nat) = (c.head : Nat) - 1 := by
  have hmove : (TM.stepConfig
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
      c).head = Configuration.moveHead (c := c) Move.left := by
    rw [seq_stepConfig_P1_normal_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])
        c (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
    simp [stepLeftOnce, hi]
  rw [hmove]
  have hne : ¬ (c.head : Nat) = 0 := by omega
  simp only [Configuration.moveHead, dif_neg hne]

/-- Step 1 (phase `0`): the tape is unchanged (the scanned bit is written back). -/
theorem seekHomeAfterRoute_step1_tape {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).tape = c.tape := by
  have hwrite : (TM.stepConfig
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
      c).tape = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P1_normal_tape stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])
        c (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
    simp [stepLeftOnce, hi]
  rw [hwrite]; funext j; by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- Step 2 (phase `1` = first `stepLeftOnce`'s accept): the `seq` handoff jumps to the shifted start of
the trailing `seqList` (the second `stepLeftOnce`), i.e. phase `2`. -/
theorem seekHomeAfterRoute_step2_phase {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 2 := by
  rw [seq_stepConfig_P1_accept_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])
      c (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate]
  decide

/-- Step 2 (handoff): the head stays put. -/
theorem seekHomeAfterRoute_step2_head {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head = c.head :=
  seq_stepConfig_P1_accept_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])
    c (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate

/-- Step 2 (handoff): the tape is unchanged. -/
theorem seekHomeAfterRoute_step2_tape {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).tape = c.tape :=
  seq_stepConfig_P1_accept_tape stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])
    c (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate

/-! ### Step 3: the second `stepLeftOnce`'s move (depth-2, phase `2`)

Phase `2` is the start of the trailing `seqList`'s P2 region (`P1.numPhases = 2`), i.e. the second
`stepLeftOnce`'s phase `0`.  Its behaviour is the outer `seq_stepConfig_P2_*` (shift by `2`) composed with
the inner `seqList`'s P1-normal transition. -/

/-- Step 3 (phase `2`, the second `stepLeftOnce`'s move): the phase advances to `3`. -/
theorem seekHomeAfterRoute_step3_phase {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 3 := by
  rw [seq_stepConfig_P2_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
      (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
  simp [seqList, seq, stepLeftOnce, hi]

/-- Step 3 (phase `2`): the head moves one cell left (when not at the left end). -/
theorem seekHomeAfterRoute_step3_head {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head : Nat) = (c.head : Nat) - 1 := by
  have hmove : (TM.stepConfig
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
      c).head = Configuration.moveHead (c := c) Move.left := by
    rw [seq_stepConfig_P2_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    simp [seqList, seq, stepLeftOnce, hi]
  rw [hmove]
  have hne : ¬ (c.head : Nat) = 0 := by omega
  simp only [Configuration.moveHead, dif_neg hne]

/-- Step 3 (phase `2`): the tape is unchanged. -/
theorem seekHomeAfterRoute_step3_tape {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).tape = c.tape := by
  have hwrite : (TM.stepConfig
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
      c).tape = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P2_tape stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    simp [seqList, seq, stepLeftOnce, hi]
  rw [hwrite]; funext j; by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
