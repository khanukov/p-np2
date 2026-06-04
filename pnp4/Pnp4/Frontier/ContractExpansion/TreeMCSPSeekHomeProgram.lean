import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepLeftProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftOneProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Home-seek after a decrement (NP-verifier track — D2 transcoder, D2t-3c-β)

The binary→unary loop body (`TM_VERIFIER_STRATEGY.md` §12, D2t-3c) keeps the unary output `U` to the
**left** of the binary counter `B`, separated by a `0`-**sentinel** (call its index `s`, the loop's
**HOME**), with `B`'s little-endian cell `0` at `s + 1`.  After one `selfLoopDecrement` pass the head
rests on the just-cleared `0`-cell at the lowest set bit `j` of `B` (index `s + 1 + j`), and the cells
strictly between the sentinel and the head (`B`'s flipped low bits) are all `1`.

`seekHomeAfterDecrement` is the composite `seq stepLeftOnce selfLoopScanLeftOne` that returns the head
to HOME: a single deterministic **left** step off the cleared `0`-cell, then a leftward
scan-over-`1`s back to the sentinel.  This module proves its run behaviour from an **arbitrary**
configuration at the seq's start phase (the head is mid-tape — it cannot be `initialConfig`, which pins
the head at `0`): given the sentinel cell is `0` and every cell strictly between it and the head is `1`,
after `(head − sentinel) + 2` steps the program rests at its accept phase `3`, the head is on the
sentinel, and the tape is unchanged.  The `j = 0` edge (head already adjacent to the sentinel) is
handled uniformly: the leftward-scan invariant admits a zero-length scan, so no case split is needed.

This builds no verifier and proves no separation; every surface carries only the standard
`[propext, Classical.choice, Quot.sound]` execution triple.  **No `P ≠ NP` claim.**
-/

/-! ### Leading two steps: `stepLeftOnce`'s move, then the `seq` handoff into `selfLoopScanLeftOne`

`stepLeftOnce` is the first (`P1`) phase of `seq stepLeftOnce selfLoopScanLeftOne`.  Its single-step
behaviour here is driven by the generic `seq_stepConfig_P1_*` lemmas (normal step at phase `0`, then the
accept-boundary handoff at phase `1`). -/

/-- Step 1 (phase `0`, `stepLeftOnce`'s move): the phase advances to `1`. -/
theorem seekHomeAfterDecrement_step1_phase {L : Nat}
    (c : Configuration (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c).state).fst.val = 1 := by
  rw [seq_stepConfig_P1_normal_phase stepLeftOnce selfLoopScanLeftOne c
      (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
  simp [stepLeftOnce, hi]

/-- Step 1 (phase `0`): the head moves left by one (when not at the left end). -/
theorem seekHomeAfterDecrement_step1_head {L : Nat}
    (c : Configuration (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) (hhead : 0 < (c.head : Nat)) :
    ((TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c).head : Nat)
      = (c.head : Nat) - 1 := by
  have hmove : (TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
    rw [seq_stepConfig_P1_normal_head stepLeftOnce selfLoopScanLeftOne c
        (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
    simp [stepLeftOnce, hi]
  rw [hmove]
  have hne : ¬ (c.head : Nat) = 0 := by omega
  simp only [Configuration.moveHead, dif_neg hne]

/-- Step 1 (phase `0`): the tape is unchanged (the scanned bit is written back). -/
theorem seekHomeAfterDecrement_step1_tape {L : Nat}
    (c : Configuration (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    rw [seq_stepConfig_P1_normal_tape stepLeftOnce selfLoopScanLeftOne c
        (h1 := by rw [hi]; decide) (hne := by rw [hi]; decide) hstate]
    simp [stepLeftOnce, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- Step 2 (phase `1` = `stepLeftOnce`'s accept): the `seq` handoff jumps to the shifted start of
`selfLoopScanLeftOne`, i.e. phase `2`. -/
theorem seekHomeAfterDecrement_step2_phase {L : Nat}
    (c : Configuration (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c).state).fst.val = 2 := by
  rw [seq_stepConfig_P1_accept_phase stepLeftOnce selfLoopScanLeftOne c
      (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate]
  decide

/-- Step 2 (handoff): the head stays put. -/
theorem seekHomeAfterDecrement_step2_head {L : Nat}
    (c : Configuration (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c).head = c.head :=
  seq_stepConfig_P1_accept_head stepLeftOnce selfLoopScanLeftOne c
    (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate

/-- Step 2 (handoff): the tape is unchanged. -/
theorem seekHomeAfterDecrement_step2_tape {L : Nat}
    (c : Configuration (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) L)
    {i : Fin (seq stepLeftOnce selfLoopScanLeftOne).numPhases} {s : Unit}
    (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c).tape = c.tape :=
  seq_stepConfig_P1_accept_tape stepLeftOnce selfLoopScanLeftOne c
    (h1 := by rw [hi]; decide) (hacc := by rw [hi]; decide) hstate

/-- The two leading steps as one run: from the seq start phase `0` with `0 < head`, after `2` steps the
phase is `2` (`selfLoopScanLeftOne`'s shifted start), the head has moved one cell left, and the tape is
unchanged.  This positions the scan exactly at the precondition of
`selfLoopScanLeftOne_seqP2_runConfig_scanning`. -/
theorem seekHomeAfterDecrement_runConfig_lead2 {L : Nat}
    (c0 : Configuration (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (hhead : 0 < (c0.head : Nat)) :
    (((TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0 2).state).fst : Nat) = 2
      ∧ ((TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0 2).head : Nat)
          = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0 2).tape = c0.tape := by
  have e2 : TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0 2
      = TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM)
          (TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0) := by
    rw [show (2 : Nat) = 1 + 1 from rfl, runConfig_add, runConfig_one, runConfig_one]
  have h1p := seekHomeAfterDecrement_step1_phase c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have h1h := seekHomeAfterDecrement_step1_head c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl hhead
  have h1t := seekHomeAfterDecrement_step1_tape c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  rw [e2]
  set c1 := TM.stepConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0 with hc1
  refine ⟨?_, ?_, ?_⟩
  · exact seekHomeAfterDecrement_step2_phase c1 (i := c1.state.fst) (s := c1.state.snd) h1p rfl
  · rw [seekHomeAfterDecrement_step2_head c1 (i := c1.state.fst) (s := c1.state.snd) h1p rfl]
    exact h1h
  · rw [seekHomeAfterDecrement_step2_tape c1 (i := c1.state.fst) (s := c1.state.snd) h1p rfl]
    exact h1t

/-! ### Home-seek run behaviour -/

/-- **Home-seek correctness.**  From an arbitrary configuration `c0` at the seq start phase `0`, if the
cell at index `sentinel` is `0` and every cell strictly between `sentinel` and the head is `1` (with
`sentinel < head`), then after `(head − sentinel) + 2` steps `seq stepLeftOnce selfLoopScanLeftOne`
(`= seekHomeAfterDecrement`) rests at its accept phase `3`, the head is on the sentinel, and the tape is
unchanged.

The `j = 0` edge (head adjacent to the sentinel, no `1`-block) is subsumed: the leftward-scan invariant
`selfLoopScanLeftOne_seqP2_runConfig_scanning` admits a zero-length scan, after which the single
terminator step stops on the sentinel. -/
theorem seekHomeAfterDecrement_runConfig_home {L : Nat}
    (c0 : Configuration (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (sentinel : Nat)
    (hlt : sentinel < (c0.head : Nat))
    (hsent : ∀ p : Fin ((seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM.tapeLength L),
      (p : Nat) = sentinel → c0.tape p = false)
    (hones : ∀ p : Fin ((seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM.tapeLength L),
      sentinel < (p : Nat) → (p : Nat) < (c0.head : Nat) → c0.tape p = true) :
    (((TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0
        (((c0.head : Nat) - sentinel) + 2)).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0
          (((c0.head : Nat) - sentinel) + 2)).head : Nat) = sentinel
      ∧ (TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0
          (((c0.head : Nat) - sentinel) + 2)).tape = c0.tape := by
  obtain ⟨hp2, hh2, ht2⟩ := seekHomeAfterDecrement_runConfig_lead2 c0 hphase (by omega)
  set c2 := TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c0 2 with hc2
  -- Scan leftward over the flipped `1`-block back to the sentinel.
  obtain ⟨hsp, hsh, hst⟩ :=
    selfLoopScanLeftOne_seqP2_runConfig_scanning stepLeftOnce c2
      (hp2.trans stepLeftOnce_numPhases.symm) ((c2.head : Nat) - sentinel) (by omega)
      (by
        intro p hp1 hp2'
        rw [ht2]
        exact hones p (by omega) (by omega))
  set c3 := TM.runConfig (M := (seq stepLeftOnce selfLoopScanLeftOne).toPhased.toTM) c2
    ((c2.head : Nat) - sentinel) with hc3
  -- Rewrite the total step count as `2 + (scan + 1)` and peel the final terminator step.
  have htot : ((c0.head : Nat) - sentinel) + 2 = 2 + (((c2.head : Nat) - sentinel) + 1) := by omega
  have hc3head : (c3.head : Nat) = sentinel := by omega
  have hi3 : (c3.state.fst).val = stepLeftOnce.numPhases := hsp
  have hbit3 : c3.tape c3.head = false := by
    rw [hst, ht2]; exact hsent c3.head hc3head
  rw [htot, runConfig_add, ← hc2, runConfig_succ, ← hc3]
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_phase stepLeftOnce c3
      (i := c3.state.fst) (s := c3.state.snd) hi3 rfl hbit3
  · rw [selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_head stepLeftOnce c3
      (i := c3.state.fst) (s := c3.state.snd) hi3 rfl hbit3]
    exact hc3head
  · rw [selfLoopScanLeftOne_seqP2_stepConfig_stop_zero_tape stepLeftOnce c3
      (i := c3.state.fst) (s := c3.state.snd) hi3 rfl hbit3, hst, ht2]

end ContractExpansion
end Frontier
end Pnp4
