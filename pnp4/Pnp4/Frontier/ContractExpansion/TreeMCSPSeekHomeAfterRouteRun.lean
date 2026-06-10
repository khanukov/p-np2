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

set_option linter.unusedSimpArgs false in
/-- Step 3 (phase `2`, the second `stepLeftOnce`'s move): the phase advances to `3`.  (The nested-`seq`
`simp` carries a redundant unfold lemma; the style linter is scoped off for this proof only.) -/
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

set_option linter.unusedSimpArgs false in
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

set_option linter.unusedSimpArgs false in
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

/-! ### Step 4: the second `stepLeftOnce`'s accept handoff (depth-2, phase `3`)

Phase `3` is the second `stepLeftOnce`'s accept (composed `P1.numPhases + stepLeftOnce.acceptPhase = 3`);
the inner `seqList`'s P1-accept handoff jumps to the start of `selfLoopScanLeft` (phase `4`). -/

set_option linter.unusedSimpArgs false in
/-- Step 4 (phase `3`, handoff): jump to phase `4` (the `selfLoopScanLeft` start). -/
theorem seekHomeAfterRoute_step4_phase {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 4 := by
  rw [seq_stepConfig_P2_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
      (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
  simp [seqList, seq, stepLeftOnce, hi]

set_option linter.unusedSimpArgs false in
/-- Step 4 (phase `3`, handoff): the head stays put. -/
theorem seekHomeAfterRoute_step4_head {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head = c.head := by
  have hmove : (TM.stepConfig
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
      c).head = Configuration.moveHead (c := c) Move.stay := by
    rw [seq_stepConfig_P2_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    simp [seqList, seq, stepLeftOnce, hi]
  rw [hmove]; simp [Configuration.moveHead]

set_option linter.unusedSimpArgs false in
/-- Step 4 (phase `3`, handoff): the tape is unchanged. -/
theorem seekHomeAfterRoute_step4_tape {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
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

/-! ### Step 5: the `selfLoopScanLeft` scan-step (depth-3, phase `4`)

Phase `4` is `selfLoopScanLeft`'s phase `0`, reached through two nested `P2` descents (composed
`P1.numPhases + P1'.numPhases = 4`).  Reading `0` it stays in phase `4` and moves the head one cell left
(scanning over the contiguous `0`-block); reading `1` it stops at phase `5`. -/

set_option linter.unusedSimpArgs false in
/-- Scan-step (phase `4`, reading `0`): stay in phase `4`, head one cell left, tape unchanged. -/
theorem seekHomeAfterRoute_scan_step {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false)
    (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 4
      ∧ ((TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [seq_stepConfig_P2_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate, hbit]
    simp [seqList, seq, selfLoopScanLeft, hi]
  · have hmove : (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head = Configuration.moveHead (c := c) Move.left := by
      rw [seq_stepConfig_P2_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
          (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate, hbit]
      simp [seqList, seq, selfLoopScanLeft, hi]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [seq_stepConfig_P2_tape stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    funext j; by_cases hj : j = c.head
    · subst hj; rw [hbit]; simp [seqList, seq, selfLoopScanLeft, hi, Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- Scan-stop (phase `4`, reading `1`): jump to phase `5` (the `selfLoopScanLeft` accept), head and tape
unchanged. -/
theorem seekHomeAfterRoute_scan_stop {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 5
      ∧ (TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).head = c.head
      ∧ (TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [seq_stepConfig_P2_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate, hbit]
    simp [seqList, seq, selfLoopScanLeft, hi]
  · have hmove : (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head = Configuration.moveHead (c := c) Move.stay := by
      rw [seq_stepConfig_P2_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
          (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate, hbit]
      simp [seqList, seq, selfLoopScanLeft, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [seq_stepConfig_P2_tape stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    funext j; by_cases hj : j = c.head
    · subst hj; rw [hbit]; simp [seqList, seq, selfLoopScanLeft, hi, Configuration.write]
    · simp [Configuration.write, hj]

/-! ### The scanning invariant (phase `4`, leftward over the `0`-block) -/

/-- **Scanning invariant.**  From phase `4` with the `m` cells `(head − m, head]` all `0`, after any
`j ≤ m` steps the program is still in phase `4`, the head has moved `j` cells left, and the tape is
unchanged. -/
theorem seekHomeAfterRoute_runConfig_scanning {L : Nat}
    (c0 : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    (hstart : (c0.state.fst : Nat) = 4) (m : Nat) (hm : m ≤ (c0.head : Nat))
    (hzeros : ∀ p : Fin ((seq stepLeftOnce
        (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - m < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false) :
    ∀ j, j ≤ m →
      (((TM.runConfig (M := (seq stepLeftOnce
            (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 j).state).fst
          : Nat) = 4
      ∧ ((TM.runConfig (M := (seq stepLeftOnce
            (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) - j
      ∧ (TM.runConfig (M := (seq stepLeftOnce
            (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 j).tape
          = c0.tape := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hstart, by simp, rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hbit : (TM.runConfig (M := (seq stepLeftOnce
          (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 j).tape
          (TM.runConfig (M := (seq stepLeftOnce
            (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 j).head = false := by
        rw [htp]; exact hzeros _ (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hhead : 0 < ((TM.runConfig (M := (seq stepLeftOnce
          (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 j).head : Nat) := by
        rw [hhd]; omega
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq stepLeftOnce
        (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 j with hc
      clear_value c
      obtain ⟨sp, sh, st⟩ := seekHomeAfterRoute_scan_step c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit hhead
      exact ⟨sp, by rw [sh, hhd]; omega, by rw [st, htp]⟩

/-! ### Steps 6–8: scan-accept handoff, the rightward step, and the final handoff -/

set_option linter.unusedSimpArgs false in
/-- Step 6 (phase `5` = `selfLoopScanLeft`'s accept): handoff to phase `6` (the `stepRightOnce` start),
head and tape unchanged. -/
theorem seekHomeAfterRoute_step6 {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 5) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 6
      ∧ (TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).head = c.head
      ∧ (TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [seq_stepConfig_P2_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi]
  · have hmove : (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head = Configuration.moveHead (c := c) Move.stay := by
      rw [seq_stepConfig_P2_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
          (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
      simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [seq_stepConfig_P2_tape stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    funext j; by_cases hj : j = c.head
    · subst hj; simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi, Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- Step 7 (phase `6` = `stepRightOnce`'s move): step one cell right (back onto the sentinel), reaching
phase `7`; tape unchanged. -/
theorem seekHomeAfterRoute_step7 {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 6) (hstate : c.state = ⟨i, s⟩)
    (hbnd : (c.head : Nat) + 1 < (seq stepLeftOnce
      (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 7
      ∧ ((TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [seq_stepConfig_P2_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi]
  · have hmove : (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head = Configuration.moveHead (c := c) Move.right := by
      rw [seq_stepConfig_P2_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
          (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
      simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [seq_stepConfig_P2_tape stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    funext j; by_cases hj : j = c.head
    · subst hj; simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi, Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- Step 8 (phase `7` = `stepRightOnce`'s accept): handoff to the trailing `idleCS` (phase `8`, the
accept), head and tape unchanged. -/
theorem seekHomeAfterRoute_step8 {L : Nat}
    (c : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).numPhases}
    {s : Unit} (hi : i.val = 7) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).state).fst.val = 8
      ∧ (TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).head = c.head
      ∧ (TM.stepConfig
          (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
          c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [seq_stepConfig_P2_phase stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi]
  · have hmove : (TM.stepConfig
        (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
        c).head = Configuration.moveHead (c := c) Move.stay := by
      rw [seq_stepConfig_P2_head stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
          (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
      simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [seq_stepConfig_P2_tape stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce]) c
        (h2 := by rw [hi]; decide) (hlt := by rw [hi]; decide) hstate]
    funext j; by_cases hj : j = c.head
    · subst hj; simp [seqList, seq, selfLoopScanLeft, stepRightOnce, hi, Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Headline: re-home from the discriminator to the sentinel

Composing the single-steps and the scanning invariant: from the discriminator (phase `0`, head `H₀`),
the run reaches the accept phase `8` with the head back on the sentinel. -/

/-- The leading four steps (phases `0→4`): from phase `0` with `2 ≤ head`, after `4` steps the program is
in phase `4`, the head has moved two cells left, and the tape is unchanged. -/
theorem seekHomeAfterRoute_runConfig_lead4 {L : Nat}
    (c0 : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    (hstart : (c0.state.fst : Nat) = 0) (hH0 : 2 ≤ (c0.head : Nat)) :
    (((TM.runConfig (M := (seq stepLeftOnce
          (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 4).state).fst
        : Nat) = 4
      ∧ ((TM.runConfig (M := (seq stepLeftOnce
          (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 4).head : Nat)
          = (c0.head : Nat) - 2
      ∧ (TM.runConfig (M := (seq stepLeftOnce
          (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 4).tape
          = c0.tape := by
  rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, TM.runConfig_succ, TM.runConfig_succ, TM.runConfig_succ,
    TM.runConfig_one]
  -- s1 = stepConfig c0 (phase 1, head H0-1)
  have hp1 := seekHomeAfterRoute_step1_phase c0 (i := c0.state.fst) (s := c0.state.snd) hstart rfl
  have hh1 := seekHomeAfterRoute_step1_head c0 (i := c0.state.fst) (s := c0.state.snd) hstart rfl
    (by omega)
  have ht1 := seekHomeAfterRoute_step1_tape c0 (i := c0.state.fst) (s := c0.state.snd) hstart rfl
  set c1 := TM.stepConfig (M := (seq stepLeftOnce
    (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 with hc1
  clear_value c1
  have hp2 := seekHomeAfterRoute_step2_phase c1 (i := c1.state.fst) (s := c1.state.snd) hp1 rfl
  have hh2 := seekHomeAfterRoute_step2_head c1 (i := c1.state.fst) (s := c1.state.snd) hp1 rfl
  have ht2 := seekHomeAfterRoute_step2_tape c1 (i := c1.state.fst) (s := c1.state.snd) hp1 rfl
  set c2 := TM.stepConfig (M := (seq stepLeftOnce
    (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c1 with hc2
  clear_value c2
  have hp3 := seekHomeAfterRoute_step3_phase c2 (i := c2.state.fst) (s := c2.state.snd) hp2 rfl
  have hh3 := seekHomeAfterRoute_step3_head c2 (i := c2.state.fst) (s := c2.state.snd) hp2 rfl
    (by rw [hh2, hh1]; omega)
  have ht3 := seekHomeAfterRoute_step3_tape c2 (i := c2.state.fst) (s := c2.state.snd) hp2 rfl
  set c3 := TM.stepConfig (M := (seq stepLeftOnce
    (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c2 with hc3
  clear_value c3
  refine ⟨seekHomeAfterRoute_step4_phase c3 (i := c3.state.fst) (s := c3.state.snd) hp3 rfl, ?_, ?_⟩
  · rw [seekHomeAfterRoute_step4_head c3 (i := c3.state.fst) (s := c3.state.snd) hp3 rfl,
      hh3, hh2, hh1]; omega
  · rw [seekHomeAfterRoute_step4_tape c3 (i := c3.state.fst) (s := c3.state.snd) hp3 rfl, ht3, ht2, ht1]

/-- **Headline.**  From the discriminator (phase `0`, head `H₀ ≥ m + 2`) with the `m` cells
`(H₀ − 2 − m, H₀ − 2]` all `0` (the sentinel + `B`'s zeros being scanned) and a `1` at `H₀ − 2 − m`
(the stopping cell = `U`'s rightmost / sentinel − 1), the run reaches the **accept phase `8`** after
`m + 8` steps with the head back on the **sentinel** `H₀ − 1 − m`, tape unchanged. -/
theorem seekHomeAfterRoute_runConfig_home {L : Nat}
    (c0 : Configuration
      (M := (seq stepLeftOnce (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) L)
    (hstart : (c0.state.fst : Nat) = 0) (m : Nat) (hm : m + 2 ≤ (c0.head : Nat))
    (hzeros : ∀ p : Fin ((seq stepLeftOnce
        (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM.tapeLength L),
      (c0.head : Nat) - 2 - m < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) - 2 → c0.tape p = false)
    (hstop : ∀ p : Fin ((seq stepLeftOnce
        (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 2 - m → c0.tape p = true)
    (hbnd : (c0.head : Nat) - 2 - m + 1 < (seq stepLeftOnce
      (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := (seq stepLeftOnce
          (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 (m + 8)).state).fst
        : Nat) = 8
      ∧ ((TM.runConfig (M := (seq stepLeftOnce
          (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 (m + 8)).head : Nat)
          = (c0.head : Nat) - 1 - m
      ∧ (TM.runConfig (M := (seq stepLeftOnce
          (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 (m + 8)).tape
          = c0.tape := by
  obtain ⟨hp4, hh4, ht4⟩ := seekHomeAfterRoute_runConfig_lead4 c0 hstart (by omega)
  -- scanning m steps from `runConfig c0 4`
  obtain ⟨hpS, hhS, htS⟩ := seekHomeAfterRoute_runConfig_scanning
    (TM.runConfig (M := (seq stepLeftOnce
      (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 4)
    hp4 m (by rw [hh4]; omega)
    (by
      intro p hp1 hp2; rw [ht4]
      exact hzeros p (by rw [hh4] at hp1; omega) (by rw [hh4] at hp2; omega)) m (le_refl m)
  rw [show (m + 8) = 4 + m + 1 + 1 + 1 + 1 from by omega,
    TM.runConfig_succ, TM.runConfig_succ, TM.runConfig_succ, TM.runConfig_succ, TM.runConfig_add]
  -- `cS = runConfig c0 (4 + m)` is at phase 4, head H0-2-m, tape c0.tape
  set cS := TM.runConfig (M := (seq stepLeftOnce
    (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM)
      (TM.runConfig (M := (seq stepLeftOnce
        (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c0 4) m with hcS
  have hpS' : (cS.state.fst : Nat) = 4 := hpS
  have hhS' : (cS.head : Nat) = (c0.head : Nat) - 2 - m := by rw [hcS, hhS, hh4]
  have htS' : cS.tape = c0.tape := by rw [hcS, htS, ht4]
  clear_value cS
  have hbitS : cS.tape cS.head = true := by rw [htS']; exact hstop _ hhS'
  obtain ⟨q5, h5h, h5t⟩ := seekHomeAfterRoute_scan_stop cS
    (i := cS.state.fst) (s := cS.state.snd) hpS' rfl hbitS
  set c5 := TM.stepConfig (M := (seq stepLeftOnce
    (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) cS with hc5
  clear_value c5
  obtain ⟨q6, h6h, h6t⟩ := seekHomeAfterRoute_step6 c5 (i := c5.state.fst) (s := c5.state.snd) q5 rfl
  set c6 := TM.stepConfig (M := (seq stepLeftOnce
    (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c5 with hc6
  clear_value c6
  have hbnd6 : ((c6.head : Nat)) + 1 < (seq stepLeftOnce
      (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM.tapeLength L := by
    rw [h6h, h5h, hhS']; exact hbnd
  obtain ⟨q7, h7h, h7t⟩ := seekHomeAfterRoute_step7 c6 (i := c6.state.fst) (s := c6.state.snd) q6 rfl hbnd6
  set c7 := TM.stepConfig (M := (seq stepLeftOnce
    (seqList [stepLeftOnce, selfLoopScanLeft, stepRightOnce])).toPhased.toTM) c6 with hc7
  clear_value c7
  obtain ⟨q8p, q8h, q8t⟩ := seekHomeAfterRoute_step8 c7 (i := c7.state.fst) (s := c7.state.snd) q7 rfl
  exact ⟨q8p, by rw [q8h, h7h, h6h, h5h, hhS']; omega, by rw [q8t, h7t, h6t, h5t, htS']⟩

end ContractExpansion
end Frontier
end Pnp4
