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

/-! ### Composition: the rightward scan-over-`1`s as a non-first (P2-region) phase

The right-only `seq`/`seqList` single-step lemmas (`seq_stepConfig_P2_*`) are transition-generic, so this
rightward scan composes as a `seq` phase exactly as `gammaSelfLoopScan` does, giving full composition-API
parity with the rest of the scan family — needed to embed it in `M`'s phase chain (`§6k` interpreter). -/

/-- Scan-over-`1`s step as a non-first phase (composition phase `P1.numPhases`, bit `1`): phase stays. -/
theorem selfLoopScanRightOne_seqP2_stepConfig_scan_one_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanRightOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopScanRightOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanRightOne, hsub, hbit]

/-- Scan-over-`1`s step as a non-first phase (bit `1`): the head moves right. -/
theorem selfLoopScanRightOne_seqP2_stepConfig_scan_one_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanRightOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopScanRightOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanRightOne, hsub, hbit]

/-- Scan-over-`1`s step as a non-first phase (bit `1`): the tape is unchanged. -/
theorem selfLoopScanRightOne_seqP2_stepConfig_scan_one_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanRightOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c).tape
      = c.write c.head true := by
    rw [seq_stepConfig_P2_tape P1 selfLoopScanRightOne c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [selfLoopScanRightOne, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Rightward scanning invariant as a non-first phase, from an arbitrary start `c0` (phase
`P1.numPhases`): if the window `[c0.head, c0.head + k)` is all `1`, then after `k` steps (with
`c0.head + k` in bounds) the phase still rests at `P1.numPhases`, the head has advanced to `c0.head + k`,
and the tape is unchanged.  Offset/non-first analogue of `selfLoopScanRightOne_runConfig_scanning`. -/
theorem selfLoopScanRightOne_seqP2_runConfig_scanning (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, (c0.head : Nat) + k < (seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L →
      (∀ p : Fin ((seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true) →
      (((TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < (seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopScanRightOne_seqP2_stepConfig_scan_one_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopScanRightOne_seqP2_stepConfig_scan_one_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopScanRightOne_seqP2_stepConfig_scan_one_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Terminator step as a non-first phase (bit `0`): jump to the shifted done phase `P1.numPhases + 1`. -/
theorem selfLoopScanRightOne_seqP2_stepConfig_stop_zero_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanRightOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopScanRightOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanRightOne, hsub, hbit]

/-- Terminator step as a non-first phase (bit `0`): the head stays put. -/
theorem selfLoopScanRightOne_seqP2_stepConfig_stop_zero_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanRightOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopScanRightOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopScanRightOne, hsub, hbit, Configuration.moveHead]

/-- Terminator step as a non-first phase (bit `0`): the tape is unchanged. -/
theorem selfLoopScanRightOne_seqP2_stepConfig_stop_zero_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopScanRightOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c).tape
      = c.write c.head false := by
    rw [seq_stepConfig_P2_tape P1 selfLoopScanRightOne c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [selfLoopScanRightOne, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Rightward terminator-locating run as a non-first phase, from an arbitrary start `c0` (phase
`P1.numPhases`): if the window `[c0.head, k)` is all `1` and cell `k` is `0` (`c0.head ≤ k`, `k` in
bounds), then after `(k − c0.head) + 1` steps the scan has stopped at the shifted done phase
`P1.numPhases + 1`, the head rests on the marker (`k`), and the tape is unchanged.  Full composition-API
parity (seqP2 scanning *and* terminator) for the rightward unary-distance seek. -/
theorem selfLoopScanRightOne_seqP2_runConfig_terminator (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (k : Nat) (hk : (c0.head : Nat) ≤ k)
    (hkb : k < (seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin ((seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < k → c0.tape p = true)
    (hterm : ∀ p : Fin ((seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0
        ((k - (c0.head : Nat)) + 1)).state).fst : Nat) = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0
          ((k - (c0.head : Nat)) + 1)).head : Nat) = k
      ∧ (TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0
          ((k - (c0.head : Nat)) + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanRightOne_seqP2_runConfig_scanning P1 c0 hphase (k - (c0.head : Nat)) (by omega)
      (fun p hp1 hp2 => hones p hp1 (by omega))
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0 (k - (c0.head : Nat))
    with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanRightOne_seqP2_stepConfig_stop_zero_phase P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopScanRightOne_seqP2_stepConfig_stop_zero_head P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopScanRightOne_seqP2_stepConfig_stop_zero_tape P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-! ### Depth-7 composition lift: rightward scan-over-`1`s as element 7 (`seqNested6`)

The *seventh* (last) element of the flattened binary→unary loop body is `selfLoopScanRightOne`, at
chain-depth 7 (`seq P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R))))))`).  The
navigation peels six `seq` levels, supplying the four non-self comparison negations `hcᵢ` and the four
middle subtraction facts `hsubᵢ` to `simp`. -/

private abbrev scanM7 (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) :=
  (seq P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R))))))).toPhased.toTM

/-- Depth-7 scan-over-`1`s step (bit `1`): the phase stays. -/
theorem selfLoopScanRightOne_seqNested6_stepConfig_scan_one_phase
    (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R))))))).numPhases}
    {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c).state).fst.val
      = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by
  have hsub : (i.val : Nat) - P1.numPhases
      = Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q.numPhases) := by
    omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q2.numPhases) := by omega
  have hc3 : ¬ (Q3.numPhases + Q4.numPhases + Q5.numPhases < Q3.numPhases) := by omega
  have hc4 : ¬ (Q4.numPhases + Q5.numPhases < Q4.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q.numPhases
      = Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q2.numPhases
      = Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub3 : Q3.numPhases + Q4.numPhases + Q5.numPhases - Q3.numPhases
      = Q4.numPhases + Q5.numPhases := by omega
  have hsub4 : Q4.numPhases + Q5.numPhases - Q4.numPhases = Q5.numPhases := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R)))))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanRightOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanRightOne, hsub, hc1, hc2, hc3, hc4, hsub1, hsub2, hsub3, hsub4, hbit]
  omega

/-- Depth-7 scan-over-`1`s step (bit `1`): the head moves right. -/
theorem selfLoopScanRightOne_seqNested6_stepConfig_scan_one_head
    (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R))))))).numPhases}
    {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c).head
      = Configuration.moveHead (c := c) Move.right := by
  have hsub : (i.val : Nat) - P1.numPhases
      = Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q.numPhases) := by
    omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q2.numPhases) := by omega
  have hc3 : ¬ (Q3.numPhases + Q4.numPhases + Q5.numPhases < Q3.numPhases) := by omega
  have hc4 : ¬ (Q4.numPhases + Q5.numPhases < Q4.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q.numPhases
      = Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q2.numPhases
      = Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub3 : Q3.numPhases + Q4.numPhases + Q5.numPhases - Q3.numPhases
      = Q4.numPhases + Q5.numPhases := by omega
  have hsub4 : Q4.numPhases + Q5.numPhases - Q4.numPhases = Q5.numPhases := by omega
  rw [seq_stepConfig_P2_head P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R)))))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanRightOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanRightOne, hsub, hc1, hc2, hc3, hc4, hsub1, hsub2, hsub3, hsub4, hbit]

/-- Depth-7 scan-over-`1`s step (bit `1`): the tape is unchanged. -/
theorem selfLoopScanRightOne_seqNested6_stepConfig_scan_one_tape
    (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R))))))).numPhases}
    {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c).tape = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases
      = Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q.numPhases) := by
    omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q2.numPhases) := by omega
  have hc3 : ¬ (Q3.numPhases + Q4.numPhases + Q5.numPhases < Q3.numPhases) := by omega
  have hc4 : ¬ (Q4.numPhases + Q5.numPhases < Q4.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q.numPhases
      = Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q2.numPhases
      = Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub3 : Q3.numPhases + Q4.numPhases + Q5.numPhases - Q3.numPhases
      = Q4.numPhases + Q5.numPhases := by omega
  have hsub4 : Q4.numPhases + Q5.numPhases - Q4.numPhases = Q5.numPhases := by omega
  have hwrite : (TM.stepConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c).tape = c.write c.head true := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R)))))) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, selfLoopScanRightOne_numPhases]; omega) hstate]
    simp [seq, selfLoopScanRightOne, hsub, hc1, hc2, hc3, hc4, hsub1, hsub2, hsub3, hsub4, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Depth-7 rightward scanning invariant from an arbitrary start `c0` (phase
`P1 + Q + Q2 + Q3 + Q4 + Q5`): the head advances over a `1`-run, phase/tape preserved.  Depth-7 analogue
of `selfLoopScanRightOne_seqP2_runConfig_scanning`. -/
theorem selfLoopScanRightOne_seqNested6_runConfig_scanning
    (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) L)
    (hphase : (c0.state.fst : Nat)
      = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases) :
    ∀ k : Nat, (c0.head : Nat) + k < (scanM7 P1 Q Q2 Q3 Q4 Q5 R).tapeLength L →
      (∀ p : Fin ((scanM7 P1 Q Q2 Q3 Q4 Q5 R).tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true) →
      (((TM.runConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c0 k).state).fst : Nat)
          = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases
      ∧ ((TM.runConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c0 k).head : Nat) = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c0 k with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < (scanM7 P1 Q Q2 Q3 Q4 Q5 R).tapeLength L := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopScanRightOne_seqNested6_stepConfig_scan_one_phase P1 Q Q2 Q3 Q4 Q5 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopScanRightOne_seqNested6_stepConfig_scan_one_head P1 Q Q2 Q3 Q4 Q5 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopScanRightOne_seqNested6_stepConfig_scan_one_tape P1 Q Q2 Q3 Q4 Q5 R c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Depth-7 terminator step (bit `0`): jump to the shifted done phase. -/
theorem selfLoopScanRightOne_seqNested6_stepConfig_stop_zero_phase
    (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R))))))).numPhases}
    {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c).state).fst.val
      = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases + 1 := by
  have hsub : (i.val : Nat) - P1.numPhases
      = Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q.numPhases) := by
    omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q2.numPhases) := by omega
  have hc3 : ¬ (Q3.numPhases + Q4.numPhases + Q5.numPhases < Q3.numPhases) := by omega
  have hc4 : ¬ (Q4.numPhases + Q5.numPhases < Q4.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q.numPhases
      = Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q2.numPhases
      = Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub3 : Q3.numPhases + Q4.numPhases + Q5.numPhases - Q3.numPhases
      = Q4.numPhases + Q5.numPhases := by omega
  have hsub4 : Q4.numPhases + Q5.numPhases - Q4.numPhases = Q5.numPhases := by omega
  rw [seq_stepConfig_P2_phase P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R)))))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanRightOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanRightOne, hsub, hc1, hc2, hc3, hc4, hsub1, hsub2, hsub3, hsub4, hbit]
  omega

/-- Depth-7 terminator step (bit `0`): the head stays put. -/
theorem selfLoopScanRightOne_seqNested6_stepConfig_stop_zero_head
    (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R))))))).numPhases}
    {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c).head = c.head := by
  have hsub : (i.val : Nat) - P1.numPhases
      = Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q.numPhases) := by
    omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q2.numPhases) := by omega
  have hc3 : ¬ (Q3.numPhases + Q4.numPhases + Q5.numPhases < Q3.numPhases) := by omega
  have hc4 : ¬ (Q4.numPhases + Q5.numPhases < Q4.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q.numPhases
      = Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q2.numPhases
      = Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub3 : Q3.numPhases + Q4.numPhases + Q5.numPhases - Q3.numPhases
      = Q4.numPhases + Q5.numPhases := by omega
  have hsub4 : Q4.numPhases + Q5.numPhases - Q4.numPhases = Q5.numPhases := by omega
  rw [seq_stepConfig_P2_head P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R)))))) c
      (h2 := by omega)
      (hlt := by simp only [seq_numPhases, selfLoopScanRightOne_numPhases]; omega) hstate]
  simp [seq, selfLoopScanRightOne, hsub, hc1, hc2, hc3, hc4, hsub1, hsub2, hsub3, hsub4, hbit,
    Configuration.moveHead]

/-- Depth-7 terminator step (bit `0`): the tape is unchanged. -/
theorem selfLoopScanRightOne_seqNested6_stepConfig_stop_zero_tape
    (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c : Configuration (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) L)
    {i : Fin (seq P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R))))))).numPhases}
    {s : Unit}
    (hi : i.val = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c).tape = c.tape := by
  have hsub : (i.val : Nat) - P1.numPhases
      = Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hc1 : ¬ (Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q.numPhases) := by
    omega
  have hc2 : ¬ (Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases < Q2.numPhases) := by omega
  have hc3 : ¬ (Q3.numPhases + Q4.numPhases + Q5.numPhases < Q3.numPhases) := by omega
  have hc4 : ¬ (Q4.numPhases + Q5.numPhases < Q4.numPhases) := by omega
  have hsub1 : Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q.numPhases
      = Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub2 : Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases - Q2.numPhases
      = Q3.numPhases + Q4.numPhases + Q5.numPhases := by omega
  have hsub3 : Q3.numPhases + Q4.numPhases + Q5.numPhases - Q3.numPhases
      = Q4.numPhases + Q5.numPhases := by omega
  have hsub4 : Q4.numPhases + Q5.numPhases - Q4.numPhases = Q5.numPhases := by omega
  have hwrite : (TM.stepConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c).tape = c.write c.head false := by
    rw [seq_stepConfig_P2_tape P1 (seq Q (seq Q2 (seq Q3 (seq Q4 (seq Q5 (seq selfLoopScanRightOne R)))))) c
        (h2 := by omega)
        (hlt := by simp only [seq_numPhases, selfLoopScanRightOne_numPhases]; omega) hstate]
    simp [seq, selfLoopScanRightOne, hsub, hc1, hc2, hc3, hc4, hsub1, hsub2, hsub3, hsub4, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Depth-7 rightward terminator-locating run from `c0` (phase `P1 + Q + Q2 + Q3 + Q4 + Q5`): if
`[c0.head, k)` are all `1` and cell `k` is `0` (`c0.head ≤ k`, `k` in bounds), then after
`(k − c0.head) + 1` steps the scan has stopped at the shifted done phase, the head rests on the marker
`k`, and the tape is unchanged.  Depth-7 analogue of `selfLoopScanRightOne_seqP2_runConfig_terminator`. -/
theorem selfLoopScanRightOne_seqNested6_runConfig_terminator
    (P1 Q Q2 Q3 Q4 Q5 R : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) L)
    (hphase : (c0.state.fst : Nat)
      = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases)
    (k : Nat) (hk : (c0.head : Nat) ≤ k) (hkb : k < (scanM7 P1 Q Q2 Q3 Q4 Q5 R).tapeLength L)
    (hones : ∀ p : Fin ((scanM7 P1 Q Q2 Q3 Q4 Q5 R).tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < k → c0.tape p = true)
    (hterm : ∀ p : Fin ((scanM7 P1 Q Q2 Q3 Q4 Q5 R).tapeLength L), (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c0 ((k - (c0.head : Nat)) + 1)).state).fst : Nat)
        = P1.numPhases + Q.numPhases + Q2.numPhases + Q3.numPhases + Q4.numPhases + Q5.numPhases + 1
      ∧ ((TM.runConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c0 ((k - (c0.head : Nat)) + 1)).head : Nat) = k
      ∧ (TM.runConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c0 ((k - (c0.head : Nat)) + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopScanRightOne_seqNested6_runConfig_scanning P1 Q Q2 Q3 Q4 Q5 R c0 hphase
      (k - (c0.head : Nat)) (by omega) (fun p hp1 hp2 => hones p hp1 (by omega))
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := scanM7 P1 Q Q2 Q3 Q4 Q5 R) c0 (k - (c0.head : Nat)) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopScanRightOne_seqNested6_stepConfig_stop_zero_phase P1 Q Q2 Q3 Q4 Q5 R c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopScanRightOne_seqNested6_stepConfig_stop_zero_head P1 Q Q2 Q3 Q4 Q5 R c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopScanRightOne_seqNested6_stepConfig_stop_zero_tape P1 Q Q2 Q3 Q4 Q5 R c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

end ContractExpansion
end Frontier
end Pnp4
