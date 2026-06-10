import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoop
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRoutePeel

/-!
# `binToUnaryLoop` base case `hbase` — `B = 0` drives the loop to its sink (NP-verifier track — D2t-3 `ε`)

The conversion loop `binToUnaryLoop = loopUntilSink binToUnaryLoopBody ⟨4⟩` (§12 `ε`) halts at the **sink
phase `4`** exactly when the binary counter `B = 0`.  This module proves that base case (`loopUntilSink`'s
`hbase`): from a HOME config at the loop's start phase whose `B`-block is all `0` with the **double
end-marker** (`1 1`) just past it, the loop's routing decision (`bZeroRouteProgram`, embedded as the outer
`seq`'s P1) scans the zeros, reads the second marker `1`, and lands in composed phase `4` — the sink — in
`z + 4` steps (`z` = the scan distance to the first marker).  On `B = 0` the head never enters the body
(phase `4 ≠ 5`, the `B > 0` target), so no navigation is needed; this is the clean half of `ε`'s
`loopUntilSink_reachesSink` (the `B > 0` `hstep` is the deferred follow-up).

Because `loopUntilSink (seq … )`'s machine has a different `tapeLength` than the standalone route's, the
route's run-through (proved generally in `TreeMCSPBZeroRouteRun*`) cannot be imported directly; it is
**re-derived inside the loop machine** here.  The loop's transition in the route region (phases `0..3`) is
evaluated by peeling the three layers: `bul_trans_route` discharges the `loopUntilSink` layer (its guards
are *Fin* equalities — refuted via the accept index `20` and the sink `4`), leaving the two `seq` layers
whose guards are *value* comparisons that `simp` resolves from the phase hypothesis.  Those `simp`s stay
out of the `runConfig` goal (the same discipline as the route's `gscan_*`/`srb_*` helpers).

**Progress classification (AGENTS.md): Infrastructure** — the `B = 0` loop-exit behaviour toward the
NP-membership leg; it proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple
only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### Single-step `stepConfig` lemmas (route region of the loop machine)

The route-region transition peel (`binToUnaryLoop_transition_route`, shared with the `decide_false` and
`hstep` bricks) lives in `TreeMCSPBinToUnaryLoopRoutePeel.lean`.

Each evaluates one step of `binToUnaryLoop`'s machine via `toTM_stepConfig_{phase,head,tape}`, peels the
`loopUntilSink` layer with `bul_trans_route`, then an isolated `simp` over the `seq` layers.  The route
writes the scanned bit back, so every step leaves the tape unchanged. -/

/-- **Scan step** (phase `0`, reading `0`): stay in phase `0`, advance the head one cell right, tape
unchanged. -/
theorem binToUnaryLoop_stepConfig_scan {L : Nat}
    (c : Configuration (M := binToUnaryLoop.toPhased.toTM) L) {i : Fin binToUnaryLoop.numPhases}
    {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false)
    (hbnd : (c.head : Nat) + 1 < binToUnaryLoop.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).state).fst.val = 0
      ∧ ((TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoop c hstate,
      binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
      stepRightThenBranch, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoop c hstate]
    have hmove : (binToUnaryLoop.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoop c hstate]
    have hbw : (binToUnaryLoop.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Scan-stop step** (phase `0`, reading `1`): jump to phase `1` (the scan's done phase), head and tape
unchanged (rests on the marker). -/
theorem binToUnaryLoop_stepConfig_stop {L : Nat}
    (c : Configuration (M := binToUnaryLoop.toPhased.toTM) L) {i : Fin binToUnaryLoop.numPhases}
    {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).state).fst.val = 1
      ∧ (TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoop c hstate,
      binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
      stepRightThenBranch, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoop c hstate]
    have hmove : (binToUnaryLoop.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoop c hstate]
    have hbw : (binToUnaryLoop.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Inner handoff step** (phase `1`): jump to phase `2` (the branch fragment's start), head and tape
unchanged. -/
theorem binToUnaryLoop_stepConfig_handoff {L : Nat}
    (c : Configuration (M := binToUnaryLoop.toPhased.toTM) L) {i : Fin binToUnaryLoop.numPhases}
    {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).state).fst.val = 2
      ∧ (TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoop c hstate,
      binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head)]
    simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
      stepRightThenBranch, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoop c hstate]
    have hmove : (binToUnaryLoop.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head)]
      simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoop c hstate]
    have hbw : (binToUnaryLoop.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head)]
      simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Branch step-right** (phase `2`): step right to the discriminator cell, reaching phase `3`; tape
unchanged. -/
theorem binToUnaryLoop_stepConfig_right {L : Nat}
    (c : Configuration (M := binToUnaryLoop.toPhased.toTM) L) {i : Fin binToUnaryLoop.numPhases}
    {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbnd : (c.head : Nat) + 1 < binToUnaryLoop.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).state).fst.val = 3
      ∧ ((TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoop c hstate,
      binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head)]
    simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
      stepRightThenBranch, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoop c hstate]
    have hmove : (binToUnaryLoop.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head)]
      simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoop c hstate]
    have hbw : (binToUnaryLoop.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head)]
      simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
        stepRightThenBranch, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- **Branch read-`1`** (phase `3`, reading `1`): jump to the composed phase `4` (the `B = 0` sink). -/
theorem binToUnaryLoop_stepConfig_branch1 {L : Nat}
    (c : Configuration (M := binToUnaryLoop.toPhased.toTM) L) {i : Fin binToUnaryLoop.numPhases}
    {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := binToUnaryLoop.toPhased.toTM) c).state).fst.val = 4 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoop c hstate,
    binToUnaryLoop_transition_route (by rw [hi]; omega) s (c.tape c.head), hbit]
  simp [binToUnaryLoopBody, binToUnaryRouteBody, bZeroRouteProgram, seq, gammaSelfLoopScan,
    stepRightThenBranch, hi]

/-! ### Run-through: `B = 0` reaches the sink phase `4` -/

/-- **Scanning invariant.**  From a HOME config `c0` at the loop's start phase (`0`) with the cells
`[c0.head, c0.head + z)` all `0`, after any `k ≤ z` steps the loop is still in phase `0`, the head has
advanced to `c0.head + k`, and the tape is unchanged. -/
theorem binToUnaryLoop_runConfig_scanning {L : Nat}
    (c0 : Configuration (M := binToUnaryLoop.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 0)
    (z : Nat) (hz : (c0.head : Nat) + z < binToUnaryLoop.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false) :
    ∀ k, k ≤ z →
      (((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hstart, rfl, rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hbit : (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 k).tape
          (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 k).head = false := by
        rw [htp]; exact hzeros _ (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : ((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 k).head : Nat) + 1
          < binToUnaryLoop.toPhased.toTM.tapeLength L := by rw [hhd]; omega
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 k with hc
      clear_value c
      obtain ⟨sp, sh, st⟩ := binToUnaryLoop_stepConfig_scan c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit hbnd
      exact ⟨sp, by rw [sh, hhd]; omega, by rw [st, htp]⟩

/-- **Terminator step.**  Adding the scan-stop marker `1` at `c0.head + z`: after `z + 1` steps the loop
is in phase `1`, head on the marker (`c0.head + z`), tape unchanged. -/
theorem binToUnaryLoop_runConfig_terminator {L : Nat}
    (c0 : Configuration (M := binToUnaryLoop.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 0)
    (z : Nat) (hz : (c0.head : Nat) + z < binToUnaryLoop.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false)
    (hterm : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z → c0.tape p = true) :
    (((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1)).head : Nat) = (c0.head : Nat) + z
      ∧ (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := binToUnaryLoop_runConfig_scanning c0 hstart z hz hzeros z (le_refl z)
  have hbit : (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 z).tape
      (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 z).head = true := by
    rw [htp]; exact hterm _ hhd
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 z with hc
  clear_value c
  obtain ⟨sp, sh, st⟩ := binToUnaryLoop_stepConfig_stop c
    (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  exact ⟨sp, by rw [sh]; exact hhd, by rw [st]; exact htp⟩

/-- **Handoff step.**  After `z + 1 + 1` steps the loop is in phase `2` (the branch fragment's start),
head still on the marker, tape unchanged. -/
theorem binToUnaryLoop_runConfig_handoff {L : Nat}
    (c0 : Configuration (M := binToUnaryLoop.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 0)
    (z : Nat) (hz : (c0.head : Nat) + z < binToUnaryLoop.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false)
    (hterm : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z → c0.tape p = true) :
    (((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1)).state).fst : Nat) = 2
      ∧ ((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1)).head : Nat) = (c0.head : Nat) + z
      ∧ (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := binToUnaryLoop_runConfig_terminator c0 hstart z hz hzeros hterm
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1) with hc
  clear_value c
  obtain ⟨sp, sh, st⟩ := binToUnaryLoop_stepConfig_handoff c
    (i := c.state.fst) (s := c.state.snd) hph rfl
  exact ⟨sp, by rw [sh]; exact hhd, by rw [st]; exact htp⟩

/-- **Branch step-right.**  After `z + 1 + 1 + 1` steps the loop has stepped right onto the discriminator
cell, reaching phase `3`, head `c0.head + z + 1`, tape unchanged. -/
theorem binToUnaryLoop_runConfig_step1 {L : Nat}
    (c0 : Configuration (M := binToUnaryLoop.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 0)
    (z : Nat) (hz1 : (c0.head : Nat) + z + 1 < binToUnaryLoop.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false)
    (hterm : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z → c0.tape p = true) :
    (((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1)).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1)).head : Nat)
          = (c0.head : Nat) + z + 1
      ∧ (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    binToUnaryLoop_runConfig_handoff c0 hstart z (by omega) hzeros hterm
  have hbnd : ((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1)).head : Nat) + 1
      < binToUnaryLoop.toPhased.toTM.tapeLength L := by rw [hhd]; omega
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1) with hc
  clear_value c
  obtain ⟨sp, sh, st⟩ := binToUnaryLoop_stepConfig_right c
    (i := c.state.fst) (s := c.state.snd) hph rfl hbnd
  exact ⟨sp, by rw [sh, hhd], by rw [st, htp]⟩

/-- **`hbase` headline.**  From a HOME config `c0` at the loop's start phase with the `B = 0` layout —
cells `[c0.head, c0.head + z)` all `0`, scan-stop marker `1` at `c0.head + z`, and the **second marker**
`1` at the discriminator `c0.head + z + 1` — the loop reaches the **sink phase `4`** after `z + 4` steps.
This is `loopUntilSink_reachesSink`'s `hbase` for `binToUnaryLoop` (the `B = 0 → sink` half of `ε`). -/
theorem binToUnaryLoop_runConfig_hbase {L : Nat}
    (c0 : Configuration (M := binToUnaryLoop.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 0)
    (z : Nat) (hz1 : (c0.head : Nat) + z + 1 < binToUnaryLoop.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + z → c0.tape p = false)
    (hterm : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z → c0.tape p = true)
    (hdisc : ∀ p : Fin (binToUnaryLoop.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + z + 1 → c0.tape p = true) :
    (((TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1 + 1)).state).fst : Nat) = 4 := by
  obtain ⟨hph, hhd, htp⟩ := binToUnaryLoop_runConfig_step1 c0 hstart z hz1 hzeros hterm
  have hbit : (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1)).tape
      (TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1)).head = true := by
    rw [htp]; exact hdisc _ hhd
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := binToUnaryLoop.toPhased.toTM) c0 (z + 1 + 1 + 1) with hc
  clear_value c
  exact binToUnaryLoop_stepConfig_branch1 c
    (i := c.state.fst) (s := c.state.snd) hph rfl hbit

end ContractExpansion
end Frontier
end Pnp4
