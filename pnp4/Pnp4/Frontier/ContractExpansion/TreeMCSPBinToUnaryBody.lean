import Pnp4.Frontier.ContractExpansion.TreeMCSPStepRightProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPSelfLoopCounter
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanRightOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPUnaryAppendLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPCounterComposition

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# The binary→unary loop body `binToUnaryBody` (NP-verifier track — D2 transcoder, D2t-3c-γ)

`binToUnaryBody` is the flattened, atomic 7-element `seqList` that performs **one pass** of the
binary→unary conversion loop (`TM_VERIFIER_STRATEGY.md` §12 D2t-3c-γ).  Working on the U-left layout

```
[ … blank | U = 1^|U| | sentinel(0) | B = b_0 b_1 … b_{w-1} | rightMarker(1) | … ]
                         ^HOME
```

one pass — from HOME with `B > 0` — decrements the binary counter `B` by one and appends one `1` to the
unary output `U`, returning the head to HOME.  The seven steps are:

1. `stepRightOnce`        — move from the sentinel onto `B`'s low cell `b_0`;
2. `selfLoopDecrement`    — borrow-decrement `B` (stops on the lowest set bit `j`);
3. `stepLeftOnce`         — step left off the just-cleared `0`-cell;
4. `selfLoopScanLeftOne`  — scan left over the flipped `1`-run back to the sentinel (HOME);
5. `stepLeftOnce`         — step left off the sentinel onto `U`'s right end;
6. `selfLoopAppendLeftOne`— scan left over `U`'s `1`s and append one `1` at its left `0`-end;
7. `selfLoopScanRightOne` — scan right over `U`'s `1`s back to the sentinel (HOME).

This module fixes the **definition** and its structural facts (`numPhases`, `timeBound`).  The seven
per-element run-behaviour segment lemmas (the depth-1…depth-7 `_seqNested…_` re-derivations) are already
proven in the element modules; the one-pass run-behaviour composition (via `seqList_run_seven`) is the
next brick.  This builds no verifier and proves no separation; all surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple.  **No `P ≠ NP` claim.**
-/

/-- One pass of the binary→unary conversion loop body, as a flattened atomic 7-element `seqList`
(§12 D2t-3c-γ).  Right-nested, so element `k` sits at chain-depth `k`. -/
def binToUnaryBody : ConstStatePhasedProgram Unit :=
  seqList [stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
    selfLoopAppendLeftOne, selfLoopScanRightOne]

/-- `binToUnaryBody` is `seq stepRightOnce (seq selfLoopDecrement R)` where `R` is the trailing
five-element `seqList` — the shape the decrement's depth-2 `_seqNested_` lemma consumes. -/
theorem binToUnaryBody_eq_seq :
    binToUnaryBody
      = seq stepRightOnce (seq selfLoopDecrement
          (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce, selfLoopAppendLeftOne,
            selfLoopScanRightOne])) := rfl

/-- The loop body has `15` phases (seven 2-phase programs plus the trailing `idleCS`). -/
@[simp] theorem binToUnaryBody_numPhases : binToUnaryBody.numPhases = 15 := rfl

/-- The loop body's start phase is `0`. -/
@[simp] theorem binToUnaryBody_startPhase_val : (binToUnaryBody.startPhase : Nat) = 0 := rfl

/-- Closed-form `timeBound`: `4·n + 10` (`stepRight 1 + decrement n + stepLeft 1 + scanLeft n +
stepLeft 1 + append n + scanRight n`, plus the seven `seqList` handoff steps).  Computed via
`seqList_timeBound_seven`; the polynomial bound the eventual `runTime_poly` accounting consumes. -/
@[simp] theorem binToUnaryBody_timeBound (n : Nat) : binToUnaryBody.timeBound n = 4 * n + 10 := by
  unfold binToUnaryBody
  rw [seqList_timeBound_seven]
  simp only [stepRightOnce_timeBound, selfLoopDecrement_timeBound, stepLeftOnce_timeBound,
    selfLoopScanLeftOne_timeBound, selfLoopAppendLeftOne_timeBound, selfLoopScanRightOne_timeBound]
  omega

/-! ### Leading two steps: `stepRightOnce`'s move, then the handoff into the decrement

`stepRightOnce` is the outermost P1 of `binToUnaryBody = seq stepRightOnce P2` (any `P2`).  These
single-step lemmas re-derive its move/handoff via the generic `seq_stepConfig_P1_*` lemmas (bound phase
parameter `i` with `hi`, the proven `seekHomeAfterDecrement` pattern), and `binToUnaryBody_runConfig_lead2`
composes the two steps for the concrete `P2 = seq selfLoopDecrement (seqList …)`: after `2` steps the
machine is at phase `2` (the decrement's shifted start), head advanced one cell right, tape unchanged —
exactly `selfLoopDecrement_seqNested_runConfig_*`'s precondition (`P1 := stepRightOnce`). -/

/-- Move step (phase `0`): the phase advances to `1`. -/
theorem binToUnaryBody_step1_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq stepRightOnce P2).toPhased.toTM) L)
    {i : Fin (seq stepRightOnce P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c).state).fst.val = 1 := by
  rw [seq_stepConfig_P1_normal_phase stepRightOnce P2 c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [stepRightOnce, hi]

/-- Move step (phase `0`): the head moves right by one (when in bounds). -/
theorem binToUnaryBody_step1_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq stepRightOnce P2).toPhased.toTM) L)
    {i : Fin (seq stepRightOnce P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hhead : (c.head : Nat) + 1 < (seq stepRightOnce P2).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  have hmove : (TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
    rw [seq_stepConfig_P1_normal_head stepRightOnce P2 c
        (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
    simp [stepRightOnce, hi]
  rw [hmove, Configuration.moveHead_right_lt c hhead]

/-- Move step (phase `0`): the tape is unchanged (the scanned bit is written back). -/
theorem binToUnaryBody_step1_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq stepRightOnce P2).toPhased.toTM) L)
    {i : Fin (seq stepRightOnce P2).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P1_normal_tape stepRightOnce P2 c
        (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
    simp [stepRightOnce, hi]
  rw [hwrite]; funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- Handoff step (phase `1` = `stepRightOnce`'s accept): the phase jumps to `P2`'s shifted start. -/
theorem binToUnaryBody_step2_phase (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq stepRightOnce P2).toPhased.toTM) L)
    {i : Fin (seq stepRightOnce P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c).state).fst.val
      = stepRightOnce.numPhases + P2.startPhase.val :=
  seq_stepConfig_P1_accept_phase stepRightOnce P2 c
    (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate

/-- Handoff step (phase `1`): the head is unchanged. -/
theorem binToUnaryBody_step2_head (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq stepRightOnce P2).toPhased.toTM) L)
    {i : Fin (seq stepRightOnce P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c).head = c.head :=
  seq_stepConfig_P1_accept_head stepRightOnce P2 c
    (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate

/-- Handoff step (phase `1`): the tape is unchanged. -/
theorem binToUnaryBody_step2_tape (P2 : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := (seq stepRightOnce P2).toPhased.toTM) L)
    {i : Fin (seq stepRightOnce P2).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq stepRightOnce P2).toPhased.toTM) c).tape = c.tape :=
  seq_stepConfig_P1_accept_tape stepRightOnce P2 c
    (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate

/-- The two leading steps as one run, on the explicit `seq` form of `binToUnaryBody`
(`binToUnaryBody_eq_seq`, `= rfl`): from start phase `0` with `head + 1` in bounds, after `2` steps the
phase is `2`, the head has advanced one cell right, and the tape is unchanged. -/
theorem binToUnaryBody_runConfig_lead2 {L : Nat}
    (c0 : Configuration (M := (seq stepRightOnce
      (seq selfLoopDecrement
        (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce, selfLoopAppendLeftOne,
          selfLoopScanRightOne]))).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) + 1 < (seq stepRightOnce
      (seq selfLoopDecrement
        (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce, selfLoopAppendLeftOne,
          selfLoopScanRightOne]))).toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := (seq stepRightOnce
        (seq selfLoopDecrement
          (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce, selfLoopAppendLeftOne,
            selfLoopScanRightOne]))).toPhased.toTM) c0 2).state).fst : Nat) = 2
      ∧ ((TM.runConfig (M := (seq stepRightOnce
          (seq selfLoopDecrement
            (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce, selfLoopAppendLeftOne,
              selfLoopScanRightOne]))).toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) + 1
      ∧ (TM.runConfig (M := (seq stepRightOnce
          (seq selfLoopDecrement
            (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce, selfLoopAppendLeftOne,
              selfLoopScanRightOne]))).toPhased.toTM) c0 2).tape = c0.tape := by
  have e2 : TM.runConfig (M := (seq stepRightOnce
        (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
          selfLoopAppendLeftOne, selfLoopScanRightOne]))).toPhased.toTM) c0 2
      = TM.stepConfig (M := (seq stepRightOnce
          (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
            selfLoopAppendLeftOne, selfLoopScanRightOne]))).toPhased.toTM)
          (TM.stepConfig (M := (seq stepRightOnce
            (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
              selfLoopAppendLeftOne, selfLoopScanRightOne]))).toPhased.toTM) c0) := by
    rw [show (2 : Nat) = 1 + 1 from rfl, runConfig_add, runConfig_one, runConfig_one]
  have h1p := binToUnaryBody_step1_phase
    (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
      selfLoopAppendLeftOne, selfLoopScanRightOne])) c0
    (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have h1h := binToUnaryBody_step1_head
    (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
      selfLoopAppendLeftOne, selfLoopScanRightOne])) c0
    (i := c0.state.fst) (s := c0.state.snd) hphase rfl hhead
  have h1t := binToUnaryBody_step1_tape
    (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
      selfLoopAppendLeftOne, selfLoopScanRightOne])) c0
    (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  rw [e2]
  set c1 := TM.stepConfig (M := (seq stepRightOnce
    (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
      selfLoopAppendLeftOne, selfLoopScanRightOne]))).toPhased.toTM) c0 with hc1
  refine ⟨?_, ?_, ?_⟩
  · have h2 := binToUnaryBody_step2_phase
      (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
        selfLoopAppendLeftOne, selfLoopScanRightOne])) c1
      (i := c1.state.fst) (s := c1.state.snd) h1p rfl
    rw [h2]; simp [seq_startPhase_val, selfLoopDecrement_startPhase_val]
  · rw [binToUnaryBody_step2_head
      (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
        selfLoopAppendLeftOne, selfLoopScanRightOne])) c1
      (i := c1.state.fst) (s := c1.state.snd) h1p rfl]
    exact h1h
  · rw [binToUnaryBody_step2_tape
      (seq selfLoopDecrement (seqList [stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
        selfLoopAppendLeftOne, selfLoopScanRightOne])) c1
      (i := c1.state.fst) (s := c1.state.snd) h1p rfl]
    exact h1t

/-! ### Next: the one-pass run composition

The seven per-element segment lemmas (`stepRightOnce` as the outermost P1 via `seq_stepConfig_P1_*`,
then `selfLoopDecrement_seqNested_*`, `stepLeftOnce_seqNested2_*`, `selfLoopScanLeftOne_seqNested3_*`,
`stepLeftOnce_seqNested4_*`, `selfLoopAppendLeftOne_seqNested5_*`, `selfLoopScanRightOne_seqNested6_*`)
compose — via `seqList_run_seven` for the time skeleton and `TM.runConfig_add` at each element boundary
— into the one-pass HOME→HOME run behaviour (`counterValue B − 1`, `|U| + 1`, head back at HOME) on the
U-left layout.  That composition is the next brick; this module fixes the definition and the structural
facts it consumes. -/

end ContractExpansion
end Frontier
end Pnp4
