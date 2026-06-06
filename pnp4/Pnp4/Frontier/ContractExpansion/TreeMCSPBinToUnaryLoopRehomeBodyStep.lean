import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehomeSeekHomeRun
import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryBody

/-!
# `binToUnaryLoopRehome` body lift — single-step lemmas (NP-verifier track — D2t-3 `ε`)

`hstep`'s fifth leg.  After the seek-HOME lift (`binToUnaryLoopRehome_seek_runConfig_home`, phase `6 → 14`)
and `handoff14` (`14 → 15`), the loop machine is at **phase `15`** = the start of `binToUnaryBody` (the
outer `seq`'s P2, then the inner `seq`'s P2).  This module re-derives `binToUnaryBody`'s **single steps**
directly on `binToUnaryLoopRehome`, at offset `+15`, via the shared body peel
`binToUnaryLoopRehome_transition_body` (phase `∉ {29, 4}`) + an isolated `simp` over the three `seq`
layers (outer P2 at `6`, inner P2 at `9`) plus `binToUnaryBody`'s own `seqList`.

Phase map (loop ↔ `binToUnaryBody` ↔ element): `15↔0` stepRight move, `16↔1` handoff, `17↔2`
decrement, `18↔3` handoff, `19↔4` stepLeft, `20↔5` handoff, `21↔6` scanLeft, `22↔7` handoff, `23↔8`
stepLeft, `24↔9` handoff, `25↔10` appendLeft, `26↔11` handoff, `27↔12` scanRight, `28↔13` handoff
(into the `idleCS` accept at `29 ↔ 14` = the loop body's accept).

The four scan work-phases (`17` decrement, `21` scanLeft, `25` appendLeft, `27` scanRight) are
bit-conditional, so each splits into a read-`1` and a read-`0` lemma.  The decrement and append phases
**write** (decrement: `1→0` stop / `0→1` borrow-right; append: `→1` always), so their tape conclusion is
`c.write c.head b'`; the moves/handoffs/pure scans write the scanned bit back (tape unchanged).

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### Element 0 — `stepRightOnce` (phases `15` move, `16` handoff) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `15`** (`stepRightOnce` move): step one cell right (off the sentinel onto `B`'s low cell),
reaching phase `16`; tape unchanged. -/
theorem binToUnaryLoopRehome_body_step15 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 15) (hstate : c.state = ⟨i, s⟩)
    (hbnd : (c.head : Nat) + 1 < binToUnaryLoopRehome.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 16
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      stepRightOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepRightOnce, hi]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepRightOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `16`** (`stepRightOnce` handoff): jump to phase `17` (the decrement start); head and tape
unchanged. -/
theorem binToUnaryLoopRehome_body_step16 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 16) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 17
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      stepRightOnce, selfLoopDecrement, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepRightOnce, selfLoopDecrement, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepRightOnce, selfLoopDecrement, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Element 1 — `selfLoopDecrement` (phase `17` work, `18` handoff) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `17`, reading `1`** (decrement hits the lowest set bit): write `0`, stay put, jump to phase
`18` (decrement accept). -/
theorem binToUnaryLoopRehome_body_step17_one {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 17) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 18
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.write c.head false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopDecrement, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopDecrement, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = false := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopDecrement, hi]
    rw [hbw]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `17`, reading `0`** (decrement borrow): write `1`, step right, stay in phase `17`. -/
theorem binToUnaryLoopRehome_body_step17_zero {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 17) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false)
    (hbnd : (c.head : Nat) + 1 < binToUnaryLoopRehome.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 17
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.write c.head true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopDecrement, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopDecrement, hi]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = true := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopDecrement, hi]
    rw [hbw]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `18`** (`selfLoopDecrement` handoff): jump to phase `19` (the stepLeft start); head and tape
unchanged. -/
theorem binToUnaryLoopRehome_body_step18 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 18) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 19
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopDecrement, stepLeftOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopDecrement, stepLeftOnce, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopDecrement, stepLeftOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Element 2 — `stepLeftOnce` (phase `19` move, `20` handoff) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `19`** (`stepLeftOnce` move): step one cell left (off the just-cleared cell), reaching phase
`20`; tape unchanged. -/
theorem binToUnaryLoopRehome_body_step19 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 19) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 20
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopDecrement, stepLeftOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopDecrement, stepLeftOnce, hi]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopDecrement, stepLeftOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `20`** (`stepLeftOnce` handoff): jump to phase `21` (the scanLeft start); head and tape
unchanged. -/
theorem binToUnaryLoopRehome_body_step20 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 20) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 21
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      stepLeftOnce, selfLoopScanLeftOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepLeftOnce, selfLoopScanLeftOne, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepLeftOnce, selfLoopScanLeftOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Element 3 — `selfLoopScanLeftOne` (phase `21` work, `22` handoff) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `21`, reading `1`** (scanLeft over the flipped run): keep the bit, step left, stay in phase
`21`. -/
theorem binToUnaryLoopRehome_body_step21_one {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 21) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true)
    (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 21
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopScanLeftOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanLeftOne, hi]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanLeftOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `21`, reading `0`** (scanLeft hits the sentinel): keep the bit, stay, jump to phase `22`. -/
theorem binToUnaryLoopRehome_body_step21_zero {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 21) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 22
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopScanLeftOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanLeftOne, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanLeftOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `22`** (`selfLoopScanLeftOne` handoff): jump to phase `23` (the second stepLeft start); head
and tape unchanged. -/
theorem binToUnaryLoopRehome_body_step22 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 22) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 23
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopScanLeftOne, stepLeftOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanLeftOne, stepLeftOnce, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanLeftOne, stepLeftOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Element 4 — `stepLeftOnce` (phase `23` move, `24` handoff) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `23`** (`stepLeftOnce` move): step one cell left (off the sentinel onto `U`'s right end),
reaching phase `24`; tape unchanged. -/
theorem binToUnaryLoopRehome_body_step23 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 23) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 24
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      stepLeftOnce, selfLoopAppendLeftOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepLeftOnce, selfLoopAppendLeftOne, hi]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepLeftOnce, selfLoopAppendLeftOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `24`** (`stepLeftOnce` handoff): jump to phase `25` (the append start); head and tape
unchanged. -/
theorem binToUnaryLoopRehome_body_step24 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 24) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 25
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      stepLeftOnce, selfLoopAppendLeftOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepLeftOnce, selfLoopAppendLeftOne, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        stepLeftOnce, selfLoopAppendLeftOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Element 5 — `selfLoopAppendLeftOne` (phase `25` work, `26` handoff) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `25`, reading `1`** (append scans over `U`'s `1`s): write `1` (keep), step left, stay in phase
`25`. -/
theorem binToUnaryLoopRehome_body_step25_one {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 25) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true)
    (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 25
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopAppendLeftOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopAppendLeftOne, hi]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopAppendLeftOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; rw [hbit]; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `25`, reading `0`** (append at `U`'s left boundary): write `1` (the appended bit), stay, jump
to phase `26`. -/
theorem binToUnaryLoopRehome_body_step25_zero {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 25) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 26
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.write c.head true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopAppendLeftOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopAppendLeftOne, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = true := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopAppendLeftOne, hi]
    rw [hbw]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `26`** (`selfLoopAppendLeftOne` handoff): jump to phase `27` (the scanRight start); head and
tape unchanged. -/
theorem binToUnaryLoopRehome_body_step26 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 26) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 27
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopAppendLeftOne, selfLoopScanRightOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopAppendLeftOne, selfLoopScanRightOne, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopAppendLeftOne, selfLoopScanRightOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Element 6 — `selfLoopScanRightOne` (phase `27` work, `28` handoff) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `27`, reading `1`** (scanRight over `U`'s `1`s back to the sentinel): keep the bit, step right,
stay in phase `27`. -/
theorem binToUnaryLoopRehome_body_step27_one {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 27) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true)
    (hbnd : (c.head : Nat) + 1 < binToUnaryLoopRehome.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 27
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopScanRightOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanRightOne, hi]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanRightOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `27`, reading `0`** (scanRight hits the sentinel = HOME): keep the bit, stay, jump to phase
`28`. -/
theorem binToUnaryLoopRehome_body_step27_zero {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 27) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 28
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopScanRightOne, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanRightOne, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanRightOne, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Phase `28`** (`selfLoopScanRightOne` handoff into the `idleCS` accept): jump to phase `29` (the loop
body's accept = the `loopUntilSink` back-edge target); head and tape unchanged. -/
theorem binToUnaryLoopRehome_body_step28 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 28) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 29
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
      selfLoopScanRightOne, idleCS, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanRightOne, idleCS, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, binToUnaryBody, seq, seqList,
        selfLoopScanRightOne, idleCS, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
