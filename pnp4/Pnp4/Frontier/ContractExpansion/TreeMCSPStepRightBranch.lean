import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaScanProgram

/-!
# `stepRightThenBranch` — read-the-next-cell routing primitive (NP-verifier track — D2t-3 routing)

The `bZeroTest` routing (`TM_VERIFIER_STRATEGY.md` §12) turns a *positional* scan-stop into a *phase*
branch by reading the cell **one to the right** of the stop (`TreeMCSPBZeroTest.lean`: the distinguishable
*spread B + double marker* layout makes that cell `1` iff `B = 0`).  This module ships the reusable
program fragment that performs exactly that read-and-branch.

`stepRightThenBranch` is a 4-phase `ConstStatePhasedProgram`:

* phase `0` (start) — **step right** one cell (writing the scanned bit back), then go to phase `1`;
* phase `1` — **read** the now-current cell and branch: `1 →` phase `2`, `0 →` phase `3`;
* phases `2` / `3` — terminal self-loops (the two branch targets; `2` is the `acceptPhase`).

Composed after a scan (its done-phase handing off to phase `0` via `seq`), phase `2`/`3` map to the
loop's *sink* / *body re-entry* — discharging the routing half of `loopUntilSink`'s `hbase`.

Following the toolkit's discipline (`loopUntilSink`, `seq` shipped structural + single-step lemmas
first), this brick ships the **definition**, `neverMovesLeft` (it only steps right or stays — so it
composes under `seqList`), the **single-step** `stepConfig` lemmas, and the **two-step `runConfig`**
branch behaviour (after `2` steps: head advanced one cell, tape unchanged, phase `= 2` or `3` by the
read bit).  Wiring this onto a concrete scan + body (mapping phases `2`/`3`) is the follow-up.

**Progress classification (AGENTS.md): Infrastructure** — a control primitive toward the NP-membership
leg; it builds no verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- Step right one cell, then read the new current cell and branch: `1 →` phase `2`, `0 →` phase `3`
(phases `2`/`3` are terminal self-loops).  See the module docstring. -/
def stepRightThenBranch : ConstStatePhasedProgram Unit where
  numPhases := 4
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨2, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.right)
    else if i.val = 1 then
      (if b then ⟨2, by omega⟩ else ⟨3, by omega⟩, (), b, Move.stay)
    else (i, (), b, Move.stay)
  timeBound := fun n => n + 2

/-- The fragment needs `2` steps to reach a branch target (`0 → 1 → 2/3`), so `timeBound` is `n + 2`,
never below `2` — under the `runTime := timeBound` whole-run semantics (`TM.run`/`TM.accepts`) the
branch is always reachable, including for `n < 2`.  (The `runConfig` lemmas below take explicit step
counts and are independent of this bound.) -/
@[simp] theorem stepRightThenBranch_timeBound (n : Nat) :
    stepRightThenBranch.timeBound n = n + 2 := rfl

/-- The fragment never moves the head left: phase `0` steps right, all other phases stay. -/
theorem stepRightThenBranch_transition_move (i : Fin 4) (s : Unit) (b : Bool) :
    (stepRightThenBranch.transition i s b).2.2.2 ≠ Move.left := by
  unfold stepRightThenBranch
  dsimp only
  split_ifs <;> simp

/-- The compiled fragment never moves its head left (lifts the transition fact through
`toPhased`/`toTM`; composes via `seqList_neverMovesLeft`). -/
theorem stepRightThenBranch_neverMovesLeft :
    TMNeverMovesLeft (stepRightThenBranch.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact stepRightThenBranch_transition_move i s b

/-! ### Single-step lemmas -/

/-- Phase `0` step: the phase advances to `1`. -/
theorem stepRightThenBranch_stepConfig_move_phase {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hi]

/-- Phase `0` step: the head advances right. -/
theorem stepRightThenBranch_stepConfig_move_head {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hi]

/-- Phase `0` step: the tape is unchanged (the scanned bit is written back). -/
theorem stepRightThenBranch_stepConfig_move_tape {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- Phase `1` step reading `1`: the phase jumps to the `true` branch target `2`. -/
theorem stepRightThenBranch_stepConfig_branch_true_phase {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hi, hbit]

/-- Phase `1` step reading `0`: the phase jumps to the `false` branch target `3`. -/
theorem stepRightThenBranch_stepConfig_branch_false_phase {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).state).fst.val = 3 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hi, hbit]

/-- Phase `1` step: the head stays put (the branch reads in place). -/
theorem stepRightThenBranch_stepConfig_branch_head {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hi, Configuration.moveHead]

/-- Phase `1` step: the tape is unchanged (the scanned bit is written back). -/
theorem stepRightThenBranch_stepConfig_branch_tape {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### Two-step run behaviour (the routing branch) -/

/-- **Branch on `1`.**  From a config in phase `0` with the cell one to the right reading `1`, after
`2` steps the fragment rests in the `true` branch target (phase `2`), head advanced one cell, tape
unchanged. -/
theorem stepRightThenBranch_runConfig_branch_true {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    (hbnd : (c.head : Nat) + 1 < stepRightThenBranch.toPhased.toTM.tapeLength L)
    (hstart : (c.state.fst : Nat) = 0)
    (hread : c.tape ⟨(c.head : Nat) + 1, hbnd⟩ = true) :
    (((TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c 2).state).fst : Nat) = 2
      ∧ ((TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c 2).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c 2).tape = c.tape := by
  have h1head := stepRightThenBranch_stepConfig_move_head c (i := c.state.fst) (s := c.state.snd) hstart rfl
  have h1tape := stepRightThenBranch_stepConfig_move_tape c (i := c.state.fst) (s := c.state.snd) hstart rfl
  have h1phase := stepRightThenBranch_stepConfig_move_phase c (i := c.state.fst) (s := c.state.snd) hstart rfl
  set c1 := TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c with hc1
  have hc1head : c1.head = ⟨(c.head : Nat) + 1, hbnd⟩ := by
    rw [h1head]; simp only [Configuration.moveHead, dif_pos hbnd]
  have hbit1 : c1.tape c1.head = true := by rw [h1tape, hc1head]; exact hread
  have hbranch := stepRightThenBranch_stepConfig_branch_true_phase c1
    (i := c1.state.fst) (s := c1.state.snd) h1phase rfl hbit1
  have hbranchhead := stepRightThenBranch_stepConfig_branch_head c1
    (i := c1.state.fst) (s := c1.state.snd) h1phase rfl
  have hbranchtape := stepRightThenBranch_stepConfig_branch_tape c1
    (i := c1.state.fst) (s := c1.state.snd) h1phase rfl
  refine ⟨?_, ?_, ?_⟩
  · show (((TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c1).state).fst : Nat) = 2
    exact hbranch
  · show ((TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c1).head : Nat) = (c.head : Nat) + 1
    rw [hbranchhead, hc1head]
  · show (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c1).tape = c.tape
    rw [hbranchtape, h1tape]

/-- **Branch on `0`.**  From a config in phase `0` with the cell one to the right reading `0`, after
`2` steps the fragment rests in the `false` branch target (phase `3`), head advanced one cell, tape
unchanged. -/
theorem stepRightThenBranch_runConfig_branch_false {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    (hbnd : (c.head : Nat) + 1 < stepRightThenBranch.toPhased.toTM.tapeLength L)
    (hstart : (c.state.fst : Nat) = 0)
    (hread : c.tape ⟨(c.head : Nat) + 1, hbnd⟩ = false) :
    (((TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c 2).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c 2).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c 2).tape = c.tape := by
  have h1head := stepRightThenBranch_stepConfig_move_head c (i := c.state.fst) (s := c.state.snd) hstart rfl
  have h1tape := stepRightThenBranch_stepConfig_move_tape c (i := c.state.fst) (s := c.state.snd) hstart rfl
  have h1phase := stepRightThenBranch_stepConfig_move_phase c (i := c.state.fst) (s := c.state.snd) hstart rfl
  set c1 := TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c with hc1
  have hc1head : c1.head = ⟨(c.head : Nat) + 1, hbnd⟩ := by
    rw [h1head]; simp only [Configuration.moveHead, dif_pos hbnd]
  have hbit1 : c1.tape c1.head = false := by rw [h1tape, hc1head]; exact hread
  have hbranch := stepRightThenBranch_stepConfig_branch_false_phase c1
    (i := c1.state.fst) (s := c1.state.snd) h1phase rfl hbit1
  have hbranchhead := stepRightThenBranch_stepConfig_branch_head c1
    (i := c1.state.fst) (s := c1.state.snd) h1phase rfl
  have hbranchtape := stepRightThenBranch_stepConfig_branch_tape c1
    (i := c1.state.fst) (s := c1.state.snd) h1phase rfl
  refine ⟨?_, ?_, ?_⟩
  · show (((TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c1).state).fst : Nat) = 3
    exact hbranch
  · show ((TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c1).head : Nat) = (c.head : Nat) + 1
    rw [hbranchhead, hc1head]
  · show (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c1).tape = c.tape
    rw [hbranchtape, h1tape]

/-! ### Terminal-phase stability (the branch targets idle)

Phases `2` and `3` (the two branch targets) are terminal self-loops.  A composition that runs the
fragment for more than its `2` branch steps (e.g. padding to a fixed `timeBound`) needs the target
phase to **persist** — these are the analogue of `gammaSelfLoopScan_runConfig_done`. -/

/-- One step at a terminal phase (`val ∉ {0, 1}`, i.e. `2`/`3`) keeps the phase, head, and tape
fixed (it writes the scanned bit back and stays). -/
theorem stepRightThenBranch_stepConfig_terminal {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hne0 : i.val ≠ 0) (hne1 : i.val ≠ 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).state).fst.val = i.val
    ∧ (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).head = c.head
    ∧ (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hne0, hne1]
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hne0, hne1, Configuration.moveHead]
  · have hwrite : (TM.stepConfig (M := stepRightThenBranch.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
      unfold TM.stepConfig
      rw [hstate]
      simp only [PhasedProgram.toTM_step]
      simp [ConstStatePhasedProgram.toPhased, stepRightThenBranch, hne0, hne1]
    rw [hwrite]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- Iterated terminal stability: from a branch-target config (phase `val ∉ {0, 1}`), running any
number of steps leaves the phase, head, and tape fixed. -/
theorem stepRightThenBranch_runConfig_terminal {L : Nat}
    (c : Configuration (M := stepRightThenBranch.toPhased.toTM) L)
    (hne0 : (c.state.fst : Nat) ≠ 0) (hne1 : (c.state.fst : Nat) ≠ 1) (k : Nat) :
    ((TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c k).state.fst : Nat) = (c.state.fst : Nat)
    ∧ (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c k).head = c.head
    ∧ (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c k).tape = c.tape := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
      obtain ⟨hph, hhd, htp⟩ := ih
      rw [TM.runConfig_succ]
      obtain ⟨hph2, hhd2, htp2⟩ :=
        stepRightThenBranch_stepConfig_terminal
          (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c k)
          (i := (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c k).state.fst)
          (s := (TM.runConfig (M := stepRightThenBranch.toPhased.toTM) c k).state.snd)
          (by rw [hph]; exact hne0) (by rw [hph]; exact hne1) rfl
      exact ⟨by rw [hph2, hph], by rw [hhd2, hhd], by rw [htp2, htp]⟩

end ContractExpansion
end Frontier
end Pnp4
