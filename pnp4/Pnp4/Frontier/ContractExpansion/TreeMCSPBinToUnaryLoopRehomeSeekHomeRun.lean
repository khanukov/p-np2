import Pnp4.Frontier.ContractExpansion.TreeMCSPBinToUnaryLoopRehomeRoutePeel

/-!
# `binToUnaryLoopRehome` seek-HOME lift — the `seekHomeAfterRoute` run-through inside the loop (NP-verifier track — D2t-3 `ε`)

`hstep`'s third leg.  After the `B > 0` route decision (`decide_false`, phase `0 → 5`) and the outer
`seq`'s P1-accept handoff (`handoff5`, phase `5 → 6`), the loop machine is at **phase `6`** = the start of
`seekHomeAfterRoute` (the outer `seq`'s P2, then the inner `seq`'s P1).  This module lifts the merged
`seekHomeAfterRoute_runConfig_home` run-through (disc → sentinel) onto `binToUnaryLoopRehome`, re-deriving
each step **directly on the loop machine** — exactly as the merged `hbase`/`decide_false` re-derived the
route region, and as `gateStreamDecoder` re-derived its per-record traversal on its own loop machine.

Each single step peels the `loopUntilSink` layer with the shared body peel
`binToUnaryLoopRehome_transition_body` (phase `∉ {29, 4}`), then an isolated `simp` evaluates the two
`seq` layers (outer P2 at offset `6`, inner P1) plus `seekHomeAfterRoute`'s own `seqList`.  Phase map
(loop ↔ `seekHomeAfterRoute`): `6 ↔ 0` (stepLeft move), `7 ↔ 1` (handoff), `8 ↔ 2` (stepLeft move),
`9 ↔ 3` (handoff), `10 ↔ 4` (scan-left), `11 ↔ 5` (handoff), `12 ↔ 6` (stepRight move), `13 ↔ 7`
(handoff), `14 ↔ 8` (the `idleCS` accept — reached, then `handoff14` hands off to the body).

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Body-region peel** (shared with the body lift): away from the loop body's accept `29` and the sink
`4`, `loopUntilSink` runs `binToUnaryLoopBodyRehome` verbatim.  Generalizes the route peel
`binToUnaryLoopRehome_transition_route` (which fixes `i < 4`) to any phase `∉ {29, 4}`. -/
theorem binToUnaryLoopRehome_transition_body {i : Fin binToUnaryLoopRehome.numPhases}
    (hne29 : (i : Nat) ≠ 29) (hne4 : (i : Nat) ≠ 4) (s : Unit) (b : Bool) :
    binToUnaryLoopRehome.transition i s b = binToUnaryLoopBodyRehome.transition i () b :=
  loopUntilSink_transition_body binToUnaryLoopBodyRehome ⟨4, by decide⟩
    (Fin.ne_of_val_ne (by rw [binToUnaryLoopBodyRehome_acceptPhase_val]; exact hne29))
    (Fin.ne_of_val_ne hne4) s b

/-! ### Single-step `stepConfig` lemmas (seek-HOME region of the loop machine, phases `6..13`)

Each peels `loopUntilSink` with `binToUnaryLoopRehome_transition_body` (the phase is neither `29` nor `4`),
then an isolated `simp` over the two `seq` layers + `seekHomeAfterRoute`'s `seqList` evaluates the step. -/

set_option linter.unusedSimpArgs false in
/-- **Step (phase `6`)** = `seekHomeAfterRoute`'s first `stepLeftOnce` move: step one cell left (off the
discriminator), reaching phase `7`; tape unchanged. -/
theorem binToUnaryLoopRehome_seek_step6 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 6) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 7
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      stepLeftOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        stepLeftOnce, hi]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        stepLeftOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- **Step (phase `7`)** = `seekHomeAfterRoute`'s first handoff: jump to phase `8`; head and tape
unchanged. -/
theorem binToUnaryLoopRehome_seek_step7 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 7) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 8
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      stepLeftOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        stepLeftOnce, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        stepLeftOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- **Step (phase `8`)** = `seekHomeAfterRoute`'s second `stepLeftOnce` move: step one cell left, reaching
phase `9`; tape unchanged. -/
theorem binToUnaryLoopRehome_seek_step8 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 8) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 9
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      stepLeftOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        stepLeftOnce, hi]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        stepLeftOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- **Step (phase `9`)** = `seekHomeAfterRoute`'s second handoff: jump to phase `10` (the
`selfLoopScanLeft` start); head and tape unchanged. -/
theorem binToUnaryLoopRehome_seek_step9 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 9) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 10
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      stepLeftOnce, selfLoopScanLeft, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        stepLeftOnce, selfLoopScanLeft, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        stepLeftOnce, selfLoopScanLeft, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- **Scan-step (phase `10`, reading `0`)** = `selfLoopScanLeft` over `B`'s `0`-block: stay in phase `10`,
head one cell left, tape unchanged. -/
theorem binToUnaryLoopRehome_seek_scan_step {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 10) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false)
    (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 10
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) - 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      selfLoopScanLeft, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.left := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, hi]
    rw [hmove]
    have hne : ¬ (c.head : Nat) = 0 := by omega
    simp only [Configuration.moveHead, dif_neg hne]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; rw [hbit]; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- **Scan-stop (phase `10`, reading `1`)** = `selfLoopScanLeft` hits `U`'s rightmost `1` (the seed): jump
to phase `11` (the scan accept); head and tape unchanged. -/
theorem binToUnaryLoopRehome_seek_scan_stop {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 10) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 11
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      selfLoopScanLeft, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head), hbit]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; rw [hbit]; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- **Step (phase `11`)** = `selfLoopScanLeft`'s accept handoff: jump to phase `12` (the `stepRightOnce`
start); head and tape unchanged. -/
theorem binToUnaryLoopRehome_seek_step11 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 11) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 12
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      selfLoopScanLeft, stepRightOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, stepRightOnce, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, stepRightOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- **Step (phase `12`)** = `seekHomeAfterRoute`'s `stepRightOnce` move: step one cell right (back onto the
sentinel), reaching phase `13`; tape unchanged. -/
theorem binToUnaryLoopRehome_seek_step12 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 12) (hstate : c.state = ⟨i, s⟩)
    (hbnd : (c.head : Nat) + 1 < binToUnaryLoopRehome.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 13
      ∧ ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      selfLoopScanLeft, stepRightOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.right := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, stepRightOnce, hi]
    rw [hmove]; simp only [Configuration.moveHead, dif_pos hbnd]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, stepRightOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

set_option linter.unusedSimpArgs false in
/-- **Step (phase `13`)** = `seekHomeAfterRoute`'s final handoff to the `idleCS` accept: jump to phase
`14`; head and tape unchanged. -/
theorem binToUnaryLoopRehome_seek_step13 {L : Nat}
    (c : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) {i : Fin binToUnaryLoopRehome.numPhases}
    {s : Unit} (hi : i.val = 13) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).state).fst.val = 14
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).head = c.head
      ∧ (TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase binToUnaryLoopRehome c hstate,
      binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
    simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
      selfLoopScanLeft, stepRightOnce, hi]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head binToUnaryLoopRehome c hstate]
    have hmove : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.2 = Move.stay := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, stepRightOnce, hi]
    rw [hmove]; simp [Configuration.moveHead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape binToUnaryLoopRehome c hstate]
    have hbw : (binToUnaryLoopRehome.transition i s (c.tape c.head)).2.2.1 = c.tape c.head := by
      rw [binToUnaryLoopRehome_transition_body (by rw [hi]; decide) (by rw [hi]; decide) s (c.tape c.head)]
      simp [binToUnaryLoopBodyRehome, binToUnaryRouteBody, seekHomeAfterRoute, seq, seqList,
        selfLoopScanLeft, stepRightOnce, hi]
    rw [hbw]; funext j; by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-! ### Run-through: re-home from the discriminator to the sentinel (loop phases `6 → 14`) -/

/-- **Scanning invariant** (phase `10`, leftward over the `0`-block).  From phase `10` with the `m` cells
`(head − m, head]` all `0`, after any `k ≤ m` steps the loop is still in phase `10`, the head has moved
`k` cells left, and the tape is unchanged. -/
theorem binToUnaryLoopRehome_seek_runConfig_scanning {L : Nat}
    (c0 : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 10)
    (m : Nat) (hm : m ≤ (c0.head : Nat))
    (hzeros : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (c0.head : Nat) - m < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false) :
    ∀ k, k ≤ m →
      (((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 k).state).fst : Nat) = 10
      ∧ ((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hstart, by simp, rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      have hbit : (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 k).tape
          (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 k).head = false := by
        rw [htp]; exact hzeros _ (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hhead : 0 < ((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 k).head : Nat) := by
        rw [hhd]; omega
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 k with hc
      clear_value c
      obtain ⟨sp, sh, st⟩ := binToUnaryLoopRehome_seek_scan_step c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit hhead
      exact ⟨sp, by rw [sh, hhd]; omega, by rw [st, htp]⟩

/-- The leading four steps (phases `6 → 10`): from phase `6` with `2 ≤ head`, after `4` steps the loop is
in phase `10`, the head has moved two cells left, and the tape is unchanged. -/
theorem binToUnaryLoopRehome_seek_runConfig_lead4 {L : Nat}
    (c0 : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 6)
    (hH0 : 2 ≤ (c0.head : Nat)) :
    (((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 4).state).fst : Nat) = 10
      ∧ ((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 4).head : Nat) = (c0.head : Nat) - 2
      ∧ (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 4).tape = c0.tape := by
  rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, TM.runConfig_succ, TM.runConfig_succ, TM.runConfig_succ,
    TM.runConfig_one]
  obtain ⟨hp1, hh1, ht1⟩ := binToUnaryLoopRehome_seek_step6 c0 (i := c0.state.fst) (s := c0.state.snd)
    hstart rfl (by omega)
  set c1 := TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 with hc1
  clear_value c1
  obtain ⟨hp2, hh2, ht2⟩ := binToUnaryLoopRehome_seek_step7 c1 (i := c1.state.fst) (s := c1.state.snd)
    hp1 rfl
  set c2 := TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c1 with hc2
  clear_value c2
  obtain ⟨hp3, hh3, ht3⟩ := binToUnaryLoopRehome_seek_step8 c2 (i := c2.state.fst) (s := c2.state.snd)
    hp2 rfl (by rw [hh2, hh1]; omega)
  set c3 := TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c2 with hc3
  clear_value c3
  obtain ⟨hp4, hh4, ht4⟩ := binToUnaryLoopRehome_seek_step9 c3 (i := c3.state.fst) (s := c3.state.snd)
    hp3 rfl
  exact ⟨hp4, by rw [hh4, hh3, hh2, hh1]; omega, by rw [ht4, ht3, ht2, ht1]⟩

/-- **Seek-HOME headline.**  From the discriminator (phase `6`, head `H₀ ≥ m + 2`) with the `m` cells
`(H₀ − 2 − m, H₀ − 2]` all `0` (the sentinel + `B`'s zeros) and a `1` at `H₀ − 2 − m` (the seed-`U`
stopping cell), the loop reaches the `seekHomeAfterRoute` accept (phase `14`) after `m + 8` steps with the
head back on the **sentinel** `H₀ − 1 − m`, tape unchanged.  This is the lift of
`seekHomeAfterRoute_runConfig_home` into `binToUnaryLoopRehome` — `hstep`'s seek-HOME leg. -/
theorem binToUnaryLoopRehome_seek_runConfig_home {L : Nat}
    (c0 : Configuration (M := binToUnaryLoopRehome.toPhased.toTM) L) (hstart : (c0.state.fst : Nat) = 6)
    (m : Nat) (hm : m + 2 ≤ (c0.head : Nat))
    (hzeros : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (c0.head : Nat) - 2 - m < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) - 2 → c0.tape p = false)
    (hstop : ∀ p : Fin (binToUnaryLoopRehome.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 2 - m → c0.tape p = true)
    (hbnd : (c0.head : Nat) - 2 - m + 1 < binToUnaryLoopRehome.toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (m + 8)).state).fst : Nat) = 14
      ∧ ((TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (m + 8)).head : Nat)
          = (c0.head : Nat) - 1 - m
      ∧ (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 (m + 8)).tape = c0.tape := by
  obtain ⟨hp4, hh4, ht4⟩ := binToUnaryLoopRehome_seek_runConfig_lead4 c0 hstart (by omega)
  obtain ⟨hpS, hhS, htS⟩ := binToUnaryLoopRehome_seek_runConfig_scanning
    (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 4)
    hp4 m (by rw [hh4]; omega)
    (by
      intro p hp1 hp2; rw [ht4]
      exact hzeros p (by rw [hh4] at hp1; omega) (by rw [hh4] at hp2; omega)) m (le_refl m)
  rw [show (m + 8) = 4 + m + 1 + 1 + 1 + 1 from by omega,
    TM.runConfig_succ, TM.runConfig_succ, TM.runConfig_succ, TM.runConfig_succ, TM.runConfig_add]
  set cS := TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM)
      (TM.runConfig (M := binToUnaryLoopRehome.toPhased.toTM) c0 4) m with hcS
  have hpS' : (cS.state.fst : Nat) = 10 := hpS
  have hhS' : (cS.head : Nat) = (c0.head : Nat) - 2 - m := by rw [hcS, hhS, hh4]
  have htS' : cS.tape = c0.tape := by rw [hcS, htS, ht4]
  clear_value cS
  have hbitS : cS.tape cS.head = true := by rw [htS']; exact hstop _ hhS'
  obtain ⟨q5, h5h, h5t⟩ := binToUnaryLoopRehome_seek_scan_stop cS
    (i := cS.state.fst) (s := cS.state.snd) hpS' rfl hbitS
  set c5 := TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) cS with hc5
  clear_value c5
  obtain ⟨q6, h6h, h6t⟩ := binToUnaryLoopRehome_seek_step11 c5 (i := c5.state.fst) (s := c5.state.snd)
    q5 rfl
  set c6 := TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c5 with hc6
  clear_value c6
  have hbnd6 : ((c6.head : Nat)) + 1 < binToUnaryLoopRehome.toPhased.toTM.tapeLength L := by
    rw [h6h, h5h, hhS']; exact hbnd
  obtain ⟨q7, h7h, h7t⟩ := binToUnaryLoopRehome_seek_step12 c6 (i := c6.state.fst) (s := c6.state.snd)
    q6 rfl hbnd6
  set c7 := TM.stepConfig (M := binToUnaryLoopRehome.toPhased.toTM) c6 with hc7
  clear_value c7
  obtain ⟨q8p, q8h, q8t⟩ := binToUnaryLoopRehome_seek_step13 c7 (i := c7.state.fst) (s := c7.state.snd)
    q7 rfl
  exact ⟨q8p, by rw [q8h, h7h, h6h, h5h, hhS']; omega, by rw [q8t, h7t, h6t, h5t, htS']⟩

end ContractExpansion
end Frontier
end Pnp4
