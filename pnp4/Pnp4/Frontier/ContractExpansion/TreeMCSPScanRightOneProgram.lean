import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

/-!
# Rightward self-loop scan over `1`s (NP-verifier track — marker-free rightward seek)

`selfLoopScanRightOne` is the **rightward** dual of `selfLoopScanLeft`/`selfLoopScanLeftOne` and the
**bit-dual** of `gammaSelfLoopScan`: a fixed 2-phase self-loop that advances the head **right** while
reading `1`s and halts (phase `1`, head resting) on the first `0`.

This is the genuine fourth member of the four-way scan vocabulary `{0,1} × {left, right}` as a *pure
traversal* (the earlier "rightward `1`" slot was filled only by `gammaSelfLoopFill`, which **writes**;
this one leaves the tape unchanged).  Its consumer is the **marker-free data-dependent rightward seek**
the on-tape gate interpreter needs (`TM_VERIFIER_STRATEGY.md` §6k): moving the head right by a
unary-encoded distance is exactly "scan right over a `1`-block, stop on the `0` past its end", so a back
reference / field stride stored in unary is followed without any tape marker.

Structure and proofs mirror `gammaSelfLoopScan` (right motion + the `dif_pos` head-bound) with the
scanned bit flipped `0 → 1`; the self-loop is `M`-compatible (a fixed 2-phase program, suitable for the
single fixed verifier `M`).
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- Rightward self-loop scan over `1`s: phase `0` re-enters itself (moving **right**) while reading a
`1`, and jumps to the "done" phase `1` (staying put) on the first `0`.  Fixed 2-phase structure —
suitable for the single fixed verifier `M`. -/
def selfLoopScanRightOne : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨0, by omega⟩, (), b, Move.right)
      else (⟨1, by omega⟩, (), b, Move.stay)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopScanRightOne_timeBound (n : Nat) :
    selfLoopScanRightOne.timeBound n = n := rfl

@[simp] theorem selfLoopScanRightOne_numPhases : selfLoopScanRightOne.numPhases = 2 := rfl

@[simp] theorem selfLoopScanRightOne_startPhase_val :
    (selfLoopScanRightOne.startPhase : Nat) = 0 := rfl

@[simp] theorem selfLoopScanRightOne_acceptPhase_val :
    (selfLoopScanRightOne.acceptPhase : Nat) = 1 := rfl

/-- The rightward scan never moves the head left: it advances right while scanning a `1`, otherwise
stays (on the terminator `0`, or in the done phase). -/
theorem selfLoopScanRightOne_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopScanRightOne.transition i s b).2.2.2 ≠ Move.left := by
  unfold selfLoopScanRightOne
  dsimp only
  split_ifs <;> simp

/-- The compiled rightward scan TM never moves its head left (lifts the transition fact through
`toPhased`/`toTM`; composes via `seqList_neverMovesLeft`). -/
theorem selfLoopScanRightOne_neverMovesLeft :
    TMNeverMovesLeft (selfLoopScanRightOne.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact selfLoopScanRightOne_transition_move i s b

/-! ### Self-loop single-step lemmas (scan phase, reading a `1`) -/

/-- Scan-phase step on a `1`: the phase stays `0` (the self-loop / back-edge). -/
theorem selfLoopScanRightOne_stepConfig_scan_one_phase {L : Nat}
    (c : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopScanRightOne.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanRightOne, hi, hbit]

/-- Scan-phase step on a `1`: the head advances right (the head-carried scan progresses). -/
theorem selfLoopScanRightOne_stepConfig_scan_one_head {L : Nat}
    (c : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopScanRightOne.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanRightOne, hi, hbit]

/-- Scan-phase step on a `1`: the tape is unchanged (the `1` is written back). -/
theorem selfLoopScanRightOne_stepConfig_scan_one_tape {L : Nat}
    (c : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopScanRightOne.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := selfLoopScanRightOne.toPhased.toTM) c).tape
      = c.write c.head true := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopScanRightOne, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-! ### Self-loop terminator step (reading the first `0`) -/

/-- Scan-phase step on a `0`: the phase jumps to the done phase `1`. -/
theorem selfLoopScanRightOne_stepConfig_stop_zero_phase {L : Nat}
    (c : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopScanRightOne.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanRightOne, hi, hbit]

/-- Scan-phase step on a `0`: the head stays put (rests on the terminator). -/
theorem selfLoopScanRightOne_stepConfig_stop_zero_head {L : Nat}
    (c : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopScanRightOne.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopScanRightOne, hi, hbit, Configuration.moveHead]

/-- Scan-phase step on a `0`: the tape is unchanged (the `0` is written back). -/
theorem selfLoopScanRightOne_stepConfig_stop_zero_tape {L : Nat}
    (c : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopScanRightOne.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := selfLoopScanRightOne.toPhased.toTM) c).tape
      = c.write c.head false := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopScanRightOne, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-! ### Run-behaviour invariants (generic start config, for composability) -/

/-- Rightward scanning invariant: from a start `c0` in scan phase `0`, if the `j` cells from the head
rightward (positions `[c0.head, c0.head + j)`) are all `1`, then after `j` steps (with
`c0.head + j` in bounds) the machine is still in scan phase `0`, the head has advanced to `c0.head + j`,
and the tape is unchanged.  The rightward dual of `selfLoopScanLeftOne_runConfig_scanning` (head
*increases*, requiring `c0.head + j < tapeLength` so each `Move.right` genuinely advances rather than
clamping at the right end). -/
theorem selfLoopScanRightOne_runConfig_scanning {L : Nat}
    (c0 : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, (c0.head : Nat) + j < selfLoopScanRightOne.toPhased.toTM.tapeLength L →
      (∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0 j).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < selfLoopScanRightOne.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopScanRightOne_stepConfig_scan_one_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopScanRightOne_stepConfig_scan_one_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopScanRightOne_stepConfig_scan_one_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Rightward terminator: from a start `c0` in scan phase `0`, if the cells `[c0.head, k)` are all `1`
and cell `k` is `0` (`c0.head ≤ k`, `k` in bounds), then after `(k − c0.head) + 1` steps the machine has
stopped at phase `1` with the head resting on the terminator (`head = k`) and the tape unchanged.  The
rightward dual of `selfLoopScanLeftOne_runConfig_terminator` — a verified "advance right over a
`1`-block to its first `0`": the marker-free **rightward seek by a unary distance** the on-tape
interpreter uses to follow a unary back-reference / field stride (`TM_VERIFIER_STRATEGY.md` §6k). -/
theorem selfLoopScanRightOne_runConfig_terminator {L : Nat}
    (c0 : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (k : Nat) (hk : (c0.head : Nat) ≤ k)
    (hkb : k < selfLoopScanRightOne.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < k → c0.tape p = true)
    (hterm : ∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0
        ((k - (c0.head : Nat)) + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0
          ((k - (c0.head : Nat)) + 1)).head : Nat) = k
      ∧ (TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0
          ((k - (c0.head : Nat)) + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanRightOne_runConfig_scanning c0 hphase (k - (c0.head : Nat)) (by omega)
      (fun p hp1 hp2 => hones p hp1 (by omega))
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0 (k - (c0.head : Nat)) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanRightOne_stepConfig_stop_zero_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopScanRightOne_stepConfig_stop_zero_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopScanRightOne_stepConfig_stop_zero_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

end ContractExpansion
end Frontier
end Pnp4
