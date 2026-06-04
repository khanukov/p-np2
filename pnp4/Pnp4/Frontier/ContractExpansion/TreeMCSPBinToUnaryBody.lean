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

This module fixes the **definition** and its structural facts (`numPhases`, `timeBound`), and assembles
the one-pass run-behaviour composition out of the per-element `_seqNested…_` segment lemmas (proven in
the element modules).  This builds no verifier and proves no separation; all surfaces carry only the
standard `[propext, Classical.choice, Quot.sound]` triple.  **No `P ≠ NP` claim.**
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

/-! ### The fully-nested `seq` unfolding `bodyFull`

The per-element segment lemmas (`stepLeftOnce_seqNested2_*`, `selfLoopScanLeftOne_seqNested3_*`, …)
are stated on the *fully `seq`-nested* form `seq P1 (seq Q (seq … (seq elem R)))`, in which the element
under analysis appears as an explicit `seq` head.  The defining `seqList` form keeps elements `3…7`
buried inside one `seqList [stepLeftOnce, …]` literal, where those lemmas cannot `rw`-fire (the literal
is not syntactically `seq stepLeftOnce …`).  `bodyFull` is the fully-nested unfolding; it is
**`rfl`-equal** to `binToUnaryBody` (the unfolding is purely `seqList_cons`/`seqList_nil`), so the
run-composition runs on `bodyFull` (where every element matches its lemma structurally) and transfers
to `binToUnaryBody` via `binToUnaryBody_eq_bodyFull`.  The `rfl` bridge and the per-element `rw`
matching through the abbrev were both verified to be fast (one abbrev delta, no whnf blow-up). -/
abbrev bodyFull : ConstStatePhasedProgram Unit :=
  seq stepRightOnce (seq selfLoopDecrement (seq stepLeftOnce
    (seq selfLoopScanLeftOne (seq stepLeftOnce (seq selfLoopAppendLeftOne
      (seq selfLoopScanRightOne (seqList [])))))))

/-- `binToUnaryBody` and its fully-nested unfolding `bodyFull` are definitionally equal (the seven-fold
`seqList_cons`/`seqList_nil` unfolding).  The run-composition is stated on `bodyFull`; this bridge
transfers it to `binToUnaryBody` for the loop. -/
theorem binToUnaryBody_eq_bodyFull : binToUnaryBody = bodyFull := rfl

/-! ### Leading two steps: `stepRightOnce`'s move, then the handoff into the decrement

`stepRightOnce` is the outermost P1 of `bodyFull = seq stepRightOnce P2` (any `P2`).  These single-step
lemmas re-derive its move/handoff via the generic `seq_stepConfig_P1_*` lemmas (bound phase parameter
`i` with `hi`), and `binToUnaryBody_runConfig_lead2` composes the two steps: after `2` steps the machine
is at phase `2` (the decrement's shifted start), head advanced one cell right, tape unchanged — exactly
`selfLoopDecrement_seqNested_runConfig_*`'s precondition (`P1 := stepRightOnce`). -/

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

/-- The two leading steps as one run, on the fully-nested `bodyFull` form: from start phase `0` with
`head + 1` in bounds, after `2` steps the phase is `2`, the head has advanced one cell right, and the
tape is unchanged. -/
theorem binToUnaryBody_runConfig_lead2 {L : Nat}
    (c0 : Configuration (M := bodyFull.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) + 1 < bodyFull.toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := bodyFull.toPhased.toTM) c0 2).state).fst : Nat) = 2
      ∧ ((TM.runConfig (M := bodyFull.toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) + 1
      ∧ (TM.runConfig (M := bodyFull.toPhased.toTM) c0 2).tape = c0.tape := by
  have e2 : TM.runConfig (M := bodyFull.toPhased.toTM) c0 2
      = TM.stepConfig (M := bodyFull.toPhased.toTM)
          (TM.stepConfig (M := bodyFull.toPhased.toTM) c0) := by
    rw [show (2 : Nat) = 1 + 1 from rfl, runConfig_add, runConfig_one, runConfig_one]
  have h1p := binToUnaryBody_step1_phase _ c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have h1h := binToUnaryBody_step1_head _ c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl hhead
  have h1t := binToUnaryBody_step1_tape _ c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  rw [e2]
  set c1 := TM.stepConfig (M := bodyFull.toPhased.toTM) c0 with hc1
  refine ⟨?_, ?_, ?_⟩
  · have h2 := binToUnaryBody_step2_phase _ c1 (i := c1.state.fst) (s := c1.state.snd) h1p rfl
    rw [h2]; simp [seq_startPhase_val, selfLoopDecrement_startPhase_val]
  · rw [binToUnaryBody_step2_head _ c1 (i := c1.state.fst) (s := c1.state.snd) h1p rfl]
    exact h1h
  · rw [binToUnaryBody_step2_tape _ c1 (i := c1.state.fst) (s := c1.state.snd) h1p rfl]
    exact h1t

/-- Run composition through element 2 (the decrement): from HOME (phase `0`, head on the sentinel) with
`B`'s low cells `[head+1, head+1+j)` all `0` and cell `head+1+j` set (`j` = lowest set bit), after
`2 + (j+1)` steps the machine is at phase `3` (decrement done, ready to hand off to element 3), the head
rests on the just-cleared cell `head+1+j`, and `B`'s low `j` cells are flipped to `1` with cell
`head+1+j` cleared.  Composes `binToUnaryBody_runConfig_lead2` (the leading 2 steps) with
`selfLoopDecrement_seqNested_runConfig_stop` (`P1 := stepRightOnce`) via `TM.runConfig_add`. -/
theorem binToUnaryBody_runConfig_afterDecrement {L : Nat}
    (c0 : Configuration (M := bodyFull.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat)
    (hj : (c0.head : Nat) + 1 + j ≤ L)
    (hbnd : (c0.head : Nat) + 1 < bodyFull.toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ hb : (c0.head : Nat) + 1 + j < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + 1 + j, hb⟩ = true) :
    (((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1))).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1))).head : Nat)
          = (c0.head : Nat) + 1 + j
      ∧ ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1))).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hp2, hh2, ht2⟩ := binToUnaryBody_runConfig_lead2 c0 hphase hbnd
  rw [TM.runConfig_add]
  set c2 := TM.runConfig (M := bodyFull.toPhased.toTM) c0 2 with hc2
  obtain ⟨hsp, hsh, hst⟩ := selfLoopDecrement_seqNested_runConfig_stop stepRightOnce _ c2
    (by rw [stepRightOnce_numPhases]; exact hp2) j (by rw [hh2]; exact hj)
    (by
      intro p hp1 hp2'
      rw [ht2]
      exact h_zeros p (by rw [hh2] at hp1; exact hp1) (by rw [hh2] at hp2'; exact hp2'))
    (by
      intro hb
      rw [ht2]
      have hcjj : (c2.head : Nat) + j = (c0.head : Nat) + 1 + j := by omega
      have hb2 : (c0.head : Nat) + 1 + j < bodyFull.toPhased.toTM.tapeLength L := by
        rw [← hcjj]; exact hb
      rw [show (⟨(c2.head : Nat) + j, hb⟩ : Fin _) = (⟨(c0.head : Nat) + 1 + j, hb2⟩ : Fin _)
        from Fin.ext hcjj]
      exact h_one hb2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsp, stepRightOnce_numPhases]
  · rw [hsh, hh2]
  · intro p; rw [hst p]; simp only [hh2, congrFun ht2 p]

/-- Run composition through the decrement→element-3 handoff: from HOME with `B`'s lowest set bit at
offset `j`, after `2 + (j+1) + 1` steps the inner `seq` has handed off out of the decrement to element 3
(`stepLeftOnce`), reaching phase `4`; head still on the cleared cell `head+1+j`, tape the decremented
pattern.  Composes `binToUnaryBody_runConfig_afterDecrement` with
`selfLoopDecrement_seqNested_stepConfig_handoff_*`. -/
theorem binToUnaryBody_runConfig_afterDecrHandoff {L : Nat}
    (c0 : Configuration (M := bodyFull.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat)
    (hj : (c0.head : Nat) + 1 + j ≤ L)
    (hbnd : (c0.head : Nat) + 1 < bodyFull.toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ hb : (c0.head : Nat) + 1 + j < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + 1 + j, hb⟩ = true) :
    (((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1)).state).fst : Nat) = 4
      ∧ ((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1)).head : Nat)
          = (c0.head : Nat) + 1 + j
      ∧ ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hap, hah, hat⟩ := binToUnaryBody_runConfig_afterDecrement c0 hphase j hj hbnd h_zeros h_one
  rw [show (2 + (j + 1) + 1) = (2 + (j + 1)) + 1 from by omega, TM.runConfig_add, TM.runConfig_one]
  set cD := TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1)) with hcD
  refine ⟨?_, ?_, ?_⟩
  · rw [selfLoopDecrement_seqNested_stepConfig_handoff_phase stepRightOnce _ cD
        (i := cD.state.fst) (s := cD.state.snd)
        (by rw [stepRightOnce_numPhases]; exact hap) rfl]
    simp [seq_startPhase_val, stepLeftOnce_startPhase_val]
  · rw [selfLoopDecrement_seqNested_stepConfig_handoff_head stepRightOnce _ cD
        (i := cD.state.fst) (s := cD.state.snd)
        (by rw [stepRightOnce_numPhases]; exact hap) rfl]
    exact hah
  · intro p
    rw [selfLoopDecrement_seqNested_stepConfig_handoff_tape stepRightOnce _ cD
        (i := cD.state.fst) (s := cD.state.snd)
        (by rw [stepRightOnce_numPhases]; exact hap) rfl]
    exact hat p

/-- Run composition through element 3 (`stepLeftOnce`): from HOME with `B`'s lowest set bit at offset
`j`, after `2 + (j+1) + 1 + 1` steps the machine has taken element 3's single left step, reaching phase
`5`; the head has moved one cell left to `head+j` (off the just-cleared cell), and the tape is the same
decremented pattern (a left step writes the scanned bit back).  Composes
`binToUnaryBody_runConfig_afterDecrHandoff` with `stepLeftOnce_seqNested2_stepConfig_*`
(`P1 := stepRightOnce`, `Q := selfLoopDecrement`) via `TM.runConfig_add`/`runConfig_one`. -/
theorem binToUnaryBody_runConfig_afterStepLeft3 {L : Nat}
    (c0 : Configuration (M := bodyFull.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat)
    (hj : (c0.head : Nat) + 1 + j ≤ L)
    (hbnd : (c0.head : Nat) + 1 < bodyFull.toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ hb : (c0.head : Nat) + 1 + j < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + 1 + j, hb⟩ = true) :
    (((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1)).state).fst : Nat) = 5
      ∧ ((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1)).head : Nat)
          = (c0.head : Nat) + j
      ∧ ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hap, hah, hat⟩ := binToUnaryBody_runConfig_afterDecrHandoff c0 hphase j hj hbnd h_zeros h_one
  rw [show (2 + (j + 1) + 1 + 1) = (2 + (j + 1) + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_one]
  set cS := TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1) with hcS
  refine ⟨?_, ?_, ?_⟩
  · rw [stepLeftOnce_seqNested2_stepConfig_phase stepRightOnce selfLoopDecrement _ cS
        (i := cS.state.fst) (s := cS.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases]; exact hap) rfl]
    rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases]
  · rw [stepLeftOnce_seqNested2_stepConfig_head stepRightOnce selfLoopDecrement _ cS
        (i := cS.state.fst) (s := cS.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases]; exact hap) rfl
        (by rw [hah]; omega)]
    rw [hah]; omega
  · intro p
    rw [stepLeftOnce_seqNested2_stepConfig_tape stepRightOnce selfLoopDecrement _ cS
        (i := cS.state.fst) (s := cS.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases]; exact hap) rfl]
    exact hat p

/-- Run composition through the element 3→4 handoff: after `2 + (j+1) + 1 + 1 + 1` steps the inner `seq`
has handed off out of `stepLeftOnce` (element 3, accept phase `5`) to element 4 (`selfLoopScanLeftOne`,
start phase `6`); head still on `B`'s flipped `1`-run at `head+j`, tape the decremented pattern.  Composes
`binToUnaryBody_runConfig_afterStepLeft3` with `stepLeftOnce_seqNested2_stepConfig_handoff_*`. -/
theorem binToUnaryBody_runConfig_afterStepLeft3Handoff {L : Nat}
    (c0 : Configuration (M := bodyFull.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat)
    (hj : (c0.head : Nat) + 1 + j ≤ L)
    (hbnd : (c0.head : Nat) + 1 < bodyFull.toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ hb : (c0.head : Nat) + 1 + j < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + 1 + j, hb⟩ = true) :
    (((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1)).state).fst : Nat) = 6
      ∧ ((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1)).head : Nat)
          = (c0.head : Nat) + j
      ∧ ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1)).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨h3p, h3h, h3t⟩ := binToUnaryBody_runConfig_afterStepLeft3 c0 hphase j hj hbnd h_zeros h_one
  rw [show (2 + (j + 1) + 1 + 1 + 1) = (2 + (j + 1) + 1 + 1) + 1 from rfl, TM.runConfig_add,
    TM.runConfig_one]
  set cS := TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1) with hcS
  refine ⟨?_, ?_, ?_⟩
  · rw [stepLeftOnce_seqNested2_stepConfig_handoff_phase stepRightOnce selfLoopDecrement _ cS
        (i := cS.state.fst) (s := cS.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases]; exact h3p) rfl]
    simp [seq_startPhase_val, selfLoopScanLeftOne_startPhase_val, stepRightOnce_numPhases,
      selfLoopDecrement_numPhases, stepLeftOnce_numPhases]
  · rw [stepLeftOnce_seqNested2_stepConfig_handoff_head stepRightOnce selfLoopDecrement _ cS
        (i := cS.state.fst) (s := cS.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases]; exact h3p) rfl]
    exact h3h
  · intro p
    rw [stepLeftOnce_seqNested2_stepConfig_handoff_tape stepRightOnce selfLoopDecrement _ cS
        (i := cS.state.fst) (s := cS.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases]; exact h3p) rfl]
    exact h3t p

/-- Run composition through element 4 (`selfLoopScanLeftOne`): from HOME with `B`'s lowest set bit at
offset `j`, after `(2 + (j+1) + 1 + 1 + 1) + (j + 1)` steps the leftward scan has retraced the
just-flipped `1`-run (`B`'s low `j` cells) and stopped on the sentinel, reaching phase `7` (the scan's
accept) with the head **back at HOME** (`c0.head`); the tape is the same decremented pattern (a scan
writes each `1` back unchanged).  This composes `binToUnaryBody_runConfig_afterStepLeft3Handoff` with
element 4's `selfLoopScanLeftOne_seqNested3_runConfig_scanning` (the `j` scan steps over the flipped run,
vacuous and correct when `j = 0`, i.e. `B` odd) followed by its `stepConfig_stop_zero_*` terminator step
on the sentinel — sidestepping the bundled `_terminator` lemma, whose `k < head` precondition would
exclude the `j = 0` case.  The precondition `h_sentinel` records the U-left invariant that HOME holds the
sentinel `0`. -/
theorem binToUnaryBody_runConfig_afterScanLeft4 {L : Nat}
    (c0 : Configuration (M := bodyFull.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat)
    (hj : (c0.head : Nat) + 1 + j ≤ L)
    (hbnd : (c0.head : Nat) + 1 < bodyFull.toPhased.toTM.tapeLength L)
    (h_zeros : ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
      (c0.head : Nat) + 1 ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + 1 + j → c0.tape p = false)
    (h_one : ∀ hb : (c0.head : Nat) + 1 + j < bodyFull.toPhased.toTM.tapeLength L,
      c0.tape ⟨(c0.head : Nat) + 1 + j, hb⟩ = true)
    (h_sentinel : c0.tape c0.head = false) :
    (((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1))).state).fst : Nat)
        = 7
      ∧ ((TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1))).head : Nat)
          = (c0.head : Nat)
      ∧ ∀ p : Fin (bodyFull.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1 + (j + 1))).tape p
            = (if (c0.head : Nat) + 1 ≤ (p : Nat) ∧ (p : Nat) < (c0.head : Nat) + 1 + j then true
                else if (p : Nat) = (c0.head : Nat) + 1 + j then false else c0.tape p) := by
  obtain ⟨hHp, hHh, hHt⟩ :=
    binToUnaryBody_runConfig_afterStepLeft3Handoff c0 hphase j hj hbnd h_zeros h_one
  rw [TM.runConfig_add]
  set cH := TM.runConfig (M := bodyFull.toPhased.toTM) c0 (2 + (j + 1) + 1 + 1 + 1) with hcH
  obtain ⟨hscp, hsch, hsct⟩ := selfLoopScanLeftOne_seqNested3_runConfig_scanning
    stepRightOnce selfLoopDecrement stepLeftOnce _ cH
    (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases, stepLeftOnce_numPhases]; exact hHp)
    j (by rw [hHh]; omega)
    (by
      intro p hp1 hp2
      rw [hHt]
      have hp1' : (c0.head : Nat) + 1 ≤ (p : Nat) := by rw [hHh] at hp1; omega
      have hp2' : (p : Nat) < (c0.head : Nat) + 1 + j := by rw [hHh] at hp2; omega
      rw [if_pos ⟨hp1', hp2'⟩])
  have hscp' : (((TM.runConfig (M := bodyFull.toPhased.toTM) cH j).state).fst : Nat) = 6 := by
    have h : (((TM.runConfig (M := bodyFull.toPhased.toTM) cH j).state).fst : Nat)
        = stepRightOnce.numPhases + selfLoopDecrement.numPhases + stepLeftOnce.numPhases := hscp
    rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases, stepLeftOnce_numPhases] at h
    exact h
  have hsch' : ((TM.runConfig (M := bodyFull.toPhased.toTM) cH j).head : Nat) = (c0.head : Nat) := by
    have h : ((TM.runConfig (M := bodyFull.toPhased.toTM) cH j).head : Nat) = (cH.head : Nat) - j := hsch
    rw [h, hHh]; omega
  have hsct' : (TM.runConfig (M := bodyFull.toPhased.toTM) cH j).tape = cH.tape := hsct
  rw [TM.runConfig_add, TM.runConfig_one]
  set c4 := TM.runConfig (M := bodyFull.toPhased.toTM) cH j with hc4
  have hfeq : c4.head = c0.head := Fin.ext hsch'
  have hbit : c4.tape c4.head = false := by
    rw [hsct', hfeq, hHt c0.head, if_neg (by omega), if_neg (by omega)]
    exact h_sentinel
  refine ⟨?_, ?_, ?_⟩
  · rw [selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_phase stepRightOnce selfLoopDecrement
        stepLeftOnce _ c4 (i := c4.state.fst) (s := c4.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases, stepLeftOnce_numPhases]; exact hscp')
        rfl hbit]
    rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases, stepLeftOnce_numPhases]
  · rw [selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_head stepRightOnce selfLoopDecrement
        stepLeftOnce _ c4 (i := c4.state.fst) (s := c4.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases, stepLeftOnce_numPhases]; exact hscp')
        rfl hbit]
    exact hsch'
  · intro p
    rw [selfLoopScanLeftOne_seqNested3_stepConfig_stop_zero_tape stepRightOnce selfLoopDecrement
        stepLeftOnce _ c4 (i := c4.state.fst) (s := c4.state.snd)
        (by rw [stepRightOnce_numPhases, selfLoopDecrement_numPhases, stepLeftOnce_numPhases]; exact hscp')
        rfl hbit, hsct']
    exact hHt p

/-! ### Next: elements 5–7 and the one-pass headline

`afterScanLeft4` returns the head to HOME (the sentinel) at phase `6`, with `B` decremented and the head
poised for element 5 (`stepLeftOnce`, depth 5) to step left off the sentinel onto `U`'s right end.  The
remaining segment lemmas — `stepLeftOnce_seqNested4_*` (element 5), `selfLoopAppendLeftOne_seqNested5_*`
(element 6, which appends one `1` to `U`), `selfLoopScanRightOne_seqNested6_*` (element 7, scan-home),
and the final terminator handoff into `idleCS` — chain on the same `bodyFull` form via `TM.runConfig_add`,
each consuming the previous checkpoint.  Elements 5–7 read/modify the U-region (the `1^|U|` block), so
they require the U-left tape invariant for `U`; that is the next brick, culminating in the one-pass
HOME→HOME headline (`counterValue B − 1`, `|U| + 1`, head back at HOME). -/

end ContractExpansion
end Frontier
end Pnp4
