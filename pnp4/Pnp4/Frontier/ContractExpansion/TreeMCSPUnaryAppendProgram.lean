import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Complexity.TMVerifier.TuringToolkit.BinaryCounter
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Self-loop unary-append (NP-verifier track — D2 transcoder, binary→unary building block)

The transcoder's binary→unary step (`TM_VERIFIER_STRATEGY.md` §11, D2t-3) builds a unary block by
appending one `1` per decrement of a scratch binary counter.  The "append one `1` to the right end of a
unary block" operation is exactly `selfLoopAppendOne`: starting on a unary block `1^k` (head at its
left end), it **scans right over the `1`s** (writing each back, tape unchanged) until the first `0`
terminator, where it **writes a single `1`** (the append) and stops — yielding `1^{k+1}`.

It is the writing dual of `selfLoopScanRightOne` (which scans the same `1`-block but stops *without*
writing) and the scan-direction analogue of `selfLoopIncrement` (identical 2-phase shape, but the
back-edge writes `1` — scanning over the block — instead of `0`).  Because it stops at the first `0`
regardless of `k`, it is a fixed 2-phase program operating on a data-dependent-width block.

This brick ships the program and its full standalone run-behaviour (scan invariant + append-stop +
done-phase idle).  The `seqP2` composition lift (to use it as a non-first phase in the binary→unary
`seq`) mirrors the other self-loops' lifts and is the follow-up.  Builds no verifier and proves no
separation; all surfaces carry only the standard `[propext, Classical.choice, Quot.sound]` triple.
-/

/-- Self-loop unary-append: phase `0` reading a `1` writes it back and advances right (scanning the
block, the back-edge); reading the first `0` writes a `1` (the append) and stops (phase `1`).  Fixed
2-phase, variable-width. -/
def selfLoopAppendOne : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨0, by omega⟩, (), true, Move.right)
      else (⟨1, by omega⟩, (), true, Move.stay)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopAppendOne_timeBound (n : Nat) : selfLoopAppendOne.timeBound n = n := rfl
@[simp] theorem selfLoopAppendOne_numPhases : selfLoopAppendOne.numPhases = 2 := rfl
@[simp] theorem selfLoopAppendOne_acceptPhase_val : selfLoopAppendOne.acceptPhase.val = 1 := rfl
@[simp] theorem selfLoopAppendOne_startPhase_val : selfLoopAppendOne.startPhase.val = 0 := rfl

/-- The append never moves the head left: it advances right while scanning, otherwise stays. -/
theorem selfLoopAppendOne_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopAppendOne.transition i s b).2.2.2 ≠ Move.left := by
  unfold selfLoopAppendOne
  dsimp only
  split_ifs <;> simp

theorem selfLoopAppendOne_neverMovesLeft : TMNeverMovesLeft (selfLoopAppendOne.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact selfLoopAppendOne_transition_move i s b

/-! ### Single-step lemmas -/

/-- Scan step (phase `0`, bit `1`): the phase stays `0` (the self-loop re-entry). -/
theorem selfLoopAppendOne_stepConfig_scan_phase {L : Nat}
    (c : Configuration (M := selfLoopAppendOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi, hbit]

/-- Scan step (phase `0`, bit `1`): the head advances right. -/
theorem selfLoopAppendOne_stepConfig_scan_head {L : Nat}
    (c : Configuration (M := selfLoopAppendOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi, hbit]

/-- Scan step (phase `0`, bit `1`): the read `1` is written back (tape unchanged at the head). -/
theorem selfLoopAppendOne_stepConfig_scan_tape {L : Nat}
    (c : Configuration (M := selfLoopAppendOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).tape = c.write c.head true := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi, hbit]

/-- Append step (phase `0`, bit `0`): the phase becomes the done phase `1`. -/
theorem selfLoopAppendOne_stepConfig_stop_phase {L : Nat}
    (c : Configuration (M := selfLoopAppendOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi, hbit]

/-- Append step (phase `0`, bit `0`): the head stays put. -/
theorem selfLoopAppendOne_stepConfig_stop_head {L : Nat}
    (c : Configuration (M := selfLoopAppendOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi, hbit, Configuration.moveHead]

/-- Append step (phase `0`, bit `0`): the terminating `0` is overwritten with `1` (the append). -/
theorem selfLoopAppendOne_stepConfig_stop_tape {L : Nat}
    (c : Configuration (M := selfLoopAppendOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).tape = c.write c.head true := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi, hbit]

/-- Scan invariant: if the first `k` cells are all `1`, then after `k ≤ L` steps the scan is still
running — phase `0`, head at `k`, and the **tape is unchanged** (each `1` is written back).  Dual of
`selfLoopIncrement_runConfig_carry` but tape-preserving (writes `1` over `1`). -/
theorem selfLoopAppendOne_runConfig_scan {L : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ L →
      (∀ p : Fin (selfLoopAppendOne.toPhased.toTM.tapeLength L),
        (p : Nat) < k →
        (selfLoopAppendOne.toPhased.toTM.initialConfig x).tape p = true) →
      (((TM.runConfig (M := selfLoopAppendOne.toPhased.toTM)
          (selfLoopAppendOne.toPhased.toTM.initialConfig x) k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopAppendOne.toPhased.toTM)
          (selfLoopAppendOne.toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ ∀ p : Fin (selfLoopAppendOne.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopAppendOne.toPhased.toTM)
            (selfLoopAppendOne.toPhased.toTM.initialConfig x) k).tape p
            = (selfLoopAppendOne.toPhased.toTM.initialConfig x).tape p := by
  intro k
  induction k with
  | zero =>
      intro _ _
      exact ⟨rfl, rfl, fun p => rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp => h1 p (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopAppendOne.toPhased.toTM)
        (selfLoopAppendOne.toPhased.toTM.initialConfig x) k with hc
      have hbnd : (c.head : Nat) + 1 < selfLoopAppendOne.toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + L + 1; omega
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega)
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopAppendOne_stepConfig_scan_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopAppendOne_stepConfig_scan_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopAppendOne_stepConfig_scan_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        intro p
        by_cases hp : p = c.head
        · subst hp
          rw [Configuration.write_self, ← htp c.head]; exact hbit.symm
        · rw [Configuration.write_other c hp true, htp p]

/-- After-append configuration: if the first `j` cells are `1` and cell `j` is `0` (`j ≤ L`), then after
`j + 1` steps the append is done — phase `1`, head on cell `j`, and the tape has cell `j` set to `1`
(everything else unchanged), so the block `[0, j]` is now `1^{j+1}`.  Combines the scan invariant at `j`
with one append step. -/
theorem selfLoopAppendOne_runConfig_stop {L : Nat} (x : Boolcube.Point L) (j : Nat) (hj : j ≤ L)
    (h_ones : ∀ p : Fin (selfLoopAppendOne.toPhased.toTM.tapeLength L),
      (p : Nat) < j → (selfLoopAppendOne.toPhased.toTM.initialConfig x).tape p = true)
    (h_zero : ∀ hb : j < selfLoopAppendOne.toPhased.toTM.tapeLength L,
      (selfLoopAppendOne.toPhased.toTM.initialConfig x).tape ⟨j, hb⟩ = false) :
    (((TM.runConfig (M := selfLoopAppendOne.toPhased.toTM)
        (selfLoopAppendOne.toPhased.toTM.initialConfig x) (j + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopAppendOne.toPhased.toTM)
          (selfLoopAppendOne.toPhased.toTM.initialConfig x) (j + 1)).head : Nat) = j
      ∧ ∀ p : Fin (selfLoopAppendOne.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopAppendOne.toPhased.toTM)
            (selfLoopAppendOne.toPhased.toTM.initialConfig x) (j + 1)).tape p
            = (if (p : Nat) = j then true
                else (selfLoopAppendOne.toPhased.toTM.initialConfig x).tape p) := by
  obtain ⟨hph, hhd, htp⟩ := selfLoopAppendOne_runConfig_scan x j hj h_ones
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopAppendOne.toPhased.toTM)
    (selfLoopAppendOne.toPhased.toTM.initialConfig x) j with hc
  have hhead_eq : c.head = ⟨j, by rw [← hhd]; exact c.head.isLt⟩ := Fin.ext hhd
  have hbit : c.tape c.head = false := by
    rw [htp, hhead_eq]; exact h_zero _
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopAppendOne_stepConfig_stop_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopAppendOne_stepConfig_stop_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhd
  · rw [selfLoopAppendOne_stepConfig_stop_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self, if_pos (by rw [hhd])]
    · rw [Configuration.write_other c hp true, htp p]
      have hpc : (p : Nat) ≠ j := fun h => hp (by rw [hhead_eq]; exact Fin.ext h)
      rw [if_neg hpc]

/-! ### Done-phase stability (idle after the append) -/

/-- A single step from the done phase (`1`) preserves the phase, head, and tape. -/
theorem selfLoopAppendOne_stepConfig_done {L : Nat}
    (c : Configuration (M := selfLoopAppendOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).state).fst.val = 1
    ∧ (TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).head = c.head
    ∧ (TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).tape = c.tape := by
  refine ⟨?_, ?_, ?_⟩
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi]
  · unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi, Configuration.moveHead]
  · have hwrite : (TM.stepConfig (M := selfLoopAppendOne.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
      unfold TM.stepConfig
      rw [hstate]
      simp only [PhasedProgram.toTM_step]
      simp [ConstStatePhasedProgram.toPhased, selfLoopAppendOne, hi]
    rw [hwrite]
    funext j
    by_cases hj : j = c.head
    · subst hj; simp [Configuration.write]
    · simp [Configuration.write, hj]

/-- Iterated done-phase stability: from a done configuration (phase `1`), running any number of steps
keeps the phase at `1`, the head fixed, and the tape unchanged. -/
theorem selfLoopAppendOne_runConfig_done {L : Nat}
    (c : Configuration (M := selfLoopAppendOne.toPhased.toTM) L)
    (hdone : (c.state.fst : Nat) = 1) (j : Nat) :
    ((TM.runConfig (M := selfLoopAppendOne.toPhased.toTM) c j).state.fst : Nat) = 1
    ∧ (TM.runConfig (M := selfLoopAppendOne.toPhased.toTM) c j).head = c.head
    ∧ (TM.runConfig (M := selfLoopAppendOne.toPhased.toTM) c j).tape = c.tape := by
  induction j with
  | zero => exact ⟨hdone, rfl, rfl⟩
  | succ j ih =>
      obtain ⟨hph, hhd, htp⟩ := ih
      rw [TM.runConfig_succ]
      obtain ⟨hph2, hhd2, htp2⟩ :=
        selfLoopAppendOne_stepConfig_done
          (TM.runConfig (M := selfLoopAppendOne.toPhased.toTM) c j)
          (i := (TM.runConfig (M := selfLoopAppendOne.toPhased.toTM) c j).state.fst)
          (s := (TM.runConfig (M := selfLoopAppendOne.toPhased.toTM) c j).state.snd) hph rfl
      exact ⟨hph2, by rw [hhd2, hhd], by rw [htp2, htp]⟩

/-! ### Composition lift: append as a non-first phase (`seqP2`)

So the append composes as the second component of `seq P1 selfLoopAppendOne` (phase offset
`P1.numPhases`).  The scan steps mirror `selfLoopScanRightOne`'s `seqP2` lift verbatim; the terminator
step differs only in that it **writes a `1`** (the append) rather than the scanned bit. -/

/-- Scan step as a non-first phase (bit `1`): the phase stays at `P1.numPhases`. -/
theorem selfLoopAppendOne_seqP2_stepConfig_scan_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopAppendOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopAppendOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c).state).fst.val
      = P1.numPhases := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopAppendOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopAppendOne, hsub, hbit]

/-- Scan step as a non-first phase (bit `1`): the head moves right. -/
theorem selfLoopAppendOne_seqP2_stepConfig_scan_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopAppendOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopAppendOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopAppendOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopAppendOne, hsub, hbit]

/-- Scan step as a non-first phase (bit `1`): the tape is unchanged (the `1` is written back). -/
theorem selfLoopAppendOne_seqP2_stepConfig_scan_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopAppendOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopAppendOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c).tape = c.tape := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  have hwrite : (TM.stepConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c).tape
      = c.write c.head true := by
    rw [seq_stepConfig_P2_tape P1 selfLoopAppendOne c
        (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
    simp [selfLoopAppendOne, hsub, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Append/terminator step as a non-first phase (bit `0`): jump to the shifted done phase
`P1.numPhases + 1`. -/
theorem selfLoopAppendOne_seqP2_stepConfig_stop_phase (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopAppendOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopAppendOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c).state).fst.val
      = P1.numPhases + 1 := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_phase P1 selfLoopAppendOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopAppendOne, hsub, hbit]

/-- Append/terminator step as a non-first phase (bit `0`): the head stays put. -/
theorem selfLoopAppendOne_seqP2_stepConfig_stop_head (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopAppendOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopAppendOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c).head = c.head := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_head P1 selfLoopAppendOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopAppendOne, hsub, hbit, Configuration.moveHead]

/-- Append/terminator step as a non-first phase (bit `0`): the terminating `0` is overwritten with `1`. -/
theorem selfLoopAppendOne_seqP2_stepConfig_stop_tape (P1 : ConstStatePhasedProgram Unit)
    {L : Nat} (c : Configuration (M := (seq P1 selfLoopAppendOne).toPhased.toTM) L)
    {i : Fin (seq P1 selfLoopAppendOne).numPhases} {s : Unit}
    (hi : i.val = P1.numPhases) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c).tape = c.write c.head true := by
  have hsub : i.val - P1.numPhases = 0 := by omega
  rw [seq_stepConfig_P2_tape P1 selfLoopAppendOne c
      (h2 := hi.ge) (hlt := by rw [hsub]; decide) hstate]
  simp [selfLoopAppendOne, hsub, hbit]

/-- Scan invariant as a non-first phase, from an arbitrary start `c0` (phase `P1.numPhases`): over a
`1^k` window the phase rests at `P1.numPhases`, head advances to `c0.head + k`, tape unchanged.  Offset
analogue of `selfLoopAppendOne_runConfig_scan`. -/
theorem selfLoopAppendOne_seqP2_runConfig_scan (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopAppendOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) :
    ∀ k : Nat, (c0.head : Nat) + k < (seq P1 selfLoopAppendOne).toPhased.toTM.tapeLength L →
      (∀ p : Fin ((seq P1 selfLoopAppendOne).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true) →
      (((TM.runConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c0 k).state).fst : Nat)
          = P1.numPhases
      ∧ ((TM.runConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < (seq P1 selfLoopAppendOne).toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopAppendOne_seqP2_stepConfig_scan_phase P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopAppendOne_seqP2_stepConfig_scan_head P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [selfLoopAppendOne_seqP2_stepConfig_scan_tape P1 c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Append run as a non-first phase, from an arbitrary start `c0` (phase `P1.numPhases`): if the window
`[c0.head, k)` is all `1` and cell `k` is `0`, then after `(k − c0.head) + 1` steps the append has
landed at the shifted done phase `P1.numPhases + 1`, the head rests on `k`, and cell `k` is now `1`
(everything else unchanged) — the unary block grew by one.  Offset analogue of
`selfLoopAppendOne_runConfig_stop`. -/
theorem selfLoopAppendOne_seqP2_runConfig_stop (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopAppendOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (k : Nat) (hk : (c0.head : Nat) ≤ k)
    (hkb : k < (seq P1 selfLoopAppendOne).toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin ((seq P1 selfLoopAppendOne).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < k → c0.tape p = true)
    (hterm : ∀ p : Fin ((seq P1 selfLoopAppendOne).toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c0
        ((k - (c0.head : Nat)) + 1)).state).fst : Nat) = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c0
          ((k - (c0.head : Nat)) + 1)).head : Nat) = k
      ∧ ∀ p : Fin ((seq P1 selfLoopAppendOne).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c0
            ((k - (c0.head : Nat)) + 1)).tape p
            = (if (p : Nat) = k then true else c0.tape p) := by
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopAppendOne_seqP2_runConfig_scan P1 c0 hphase (k - (c0.head : Nat)) (by omega)
      (fun p hp1 hp2 => hones p hp1 (by omega))
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (seq P1 selfLoopAppendOne).toPhased.toTM) c0 (k - (c0.head : Nat))
    with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hhead_eq : c.head = ⟨k, by rw [← hhdk]; exact c.head.isLt⟩ := Fin.ext hhdk
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopAppendOne_seqP2_stepConfig_stop_phase P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopAppendOne_seqP2_stepConfig_stop_head P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopAppendOne_seqP2_stepConfig_stop_tape P1 c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self, if_pos hhdk]
    · rw [Configuration.write_other c hp true, congrFun htp p]
      have hpc : (p : Nat) ≠ k := fun h => hp (by rw [hhead_eq]; exact Fin.ext h)
      rw [if_neg hpc]

end ContractExpansion
end Frontier
end Pnp4
