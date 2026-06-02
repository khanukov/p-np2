import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Count-zeros scan program (NP-verifier track, gamma-decode phase — first brick)

The Elias-gamma block decoded by the parser is `0^z 1 b₁…b_z` with `z = bitLength (n+1) − 1`; the
first step of decoding it on the tape is to **locate the unary terminator** (the first `1`) by
scanning rightward over the leading zeros.  This module builds that scan as a uniform-state phased
program and establishes its structural facts (`timeBound`, never-moves-left); the semantic invariant
(after the scan the head rests on the terminator, so the leading-zero count `z` equals
`head − scanStart`) is the next brick.

Design (see `TM_VERIFIER_STRATEGY.md` §6b, approach 2, "head-carried scan"): the control state is a
single `Bool` — `true` = "still scanning for the terminator".  Each active step keeps scanning iff it
was scanning *and* read a `0`; the new state is therefore `s && !b`, and the head advances (`right`)
exactly when scanning continues, otherwise it stays.  So on the first `1` (or once stopped) the
machine freezes in place — the head is left on the terminator cell and `z` is read off as a head
offset, with no separate counter.  The scan runs for a fixed `maxIters` steps (an upper bound on the
gamma length, e.g. `bitLength N`); `maxIters ≥ z + 1` suffices for the head to reach the terminator.

This is one sub-step of one parse phase; on its own it builds no verifier and proves no separation.
-/

/-- Scan rightward to the first `1`-cell.  State `Bool` = "still scanning"; while scanning and the
read bit is `0`, advance right (keep scanning); on a `1` (or once stopped) stay and stop. -/
def gammaZeroScanProgram (maxIters : Nat) : ConstStatePhasedProgram Bool where
  numPhases := maxIters + 1
  startPhase := ⟨0, by omega⟩
  startState := true
  acceptPhase := ⟨maxIters, by omega⟩
  acceptState := false
  transition := fun i s b =>
    if h : i.val < maxIters then
      (⟨i.val + 1, by omega⟩, s && !b, b, cond (s && !b) Move.right Move.stay)
    else
      (⟨maxIters, by omega⟩, s, b, Move.stay)
  timeBound := fun _ => maxIters

@[simp] theorem gammaZeroScanProgram_timeBound (maxIters n : Nat) :
    (gammaZeroScanProgram maxIters).timeBound n = maxIters := rfl

/-- The count-zeros scan never moves the head left: it advances right while scanning, otherwise
stays. -/
theorem gammaZeroScanProgram_transition_move (maxIters : Nat)
    (i : Fin (maxIters + 1)) (s b : Bool) :
    ((gammaZeroScanProgram maxIters).transition i s b).2.2.2 ≠ Move.left := by
  unfold gammaZeroScanProgram
  dsimp only
  split
  · cases s <;> cases b <;> simp
  · simp

/-- The compiled count-zeros scan TM never moves its head left, lifting
`gammaZeroScanProgram_transition_move` through `toPhased`/`toTM`.  Feeds head-position tracking in the
forthcoming scan invariant (and `seqList_neverMovesLeft` when this phase is composed). -/
theorem gammaZeroScanProgram_neverMovesLeft (maxIters : Nat) :
    TMNeverMovesLeft ((gammaZeroScanProgram maxIters).toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact gammaZeroScanProgram_transition_move maxIters i s b

/-! ## Single-step behaviour (phase < maxIters)

The per-step lemmas for an active scan phase, mirroring the tag-check program's single-step lemmas:
the phase advances by one; the accumulated "still scanning" flag becomes `s && !(read bit)`; the tape
is unchanged (the read bit is written back); and the head moves according to
`cond (s && !(read bit)) right stay` (advance while scanning a `0`, stay otherwise).  These feed the
forthcoming scan invariant. -/

/-- One active step advances the phase index by one. -/
theorem gammaZeroScanProgram_stepConfig_phase {L maxIters : Nat}
    (c : Configuration (M := (gammaZeroScanProgram maxIters).toPhased.toTM) L)
    {i : Fin (maxIters + 1)} {s : Bool} (hi : i.val < maxIters)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM) c).state).fst.val
      = i.val + 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, gammaZeroScanProgram, dif_pos hi]

/-- One active step updates the "still scanning" flag to `s && !(read bit)`. -/
theorem gammaZeroScanProgram_stepConfig_state {L maxIters : Nat}
    (c : Configuration (M := (gammaZeroScanProgram maxIters).toPhased.toTM) L)
    {i : Fin (maxIters + 1)} {s : Bool} (hi : i.val < maxIters)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM) c).state).snd
      = (s && !(c.tape c.head)) := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, gammaZeroScanProgram, dif_pos hi]

/-- One active step leaves the tape unchanged (it writes back the bit it read). -/
theorem gammaZeroScanProgram_stepConfig_tape {L maxIters : Nat}
    (c : Configuration (M := (gammaZeroScanProgram maxIters).toPhased.toTM) L)
    {i : Fin (maxIters + 1)} {s : Bool} (hi : i.val < maxIters)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp only [ConstStatePhasedProgram.toPhased, gammaZeroScanProgram, dif_pos hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One active step moves the head by `cond (s && !(read bit)) right stay`: it advances right while
still scanning a `0`, and stays once it reads a `1` (or has stopped). -/
theorem gammaZeroScanProgram_stepConfig_head {L maxIters : Nat}
    (c : Configuration (M := (gammaZeroScanProgram maxIters).toPhased.toTM) L)
    {i : Fin (maxIters + 1)} {s : Bool} (hi : i.val < maxIters)
    (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) (cond (s && !(c.tape c.head)) Move.right Move.stay) := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp only [ConstStatePhasedProgram.toPhased, gammaZeroScanProgram, dif_pos hi]

/-- Scanning-regime invariant: if the first `k` cells are all `0`, then after `k ≤ maxIters` steps
from the initial configuration the scan is still in progress — the phase and head are both at `k`,
the "still scanning" flag is `true`, and the tape is unchanged.  Proved by induction on `k` using the
single-step lemmas; the conditional head advance fires because every scanned bit is `0`.  (This is the
analogue of `tagCheckProgram_runConfig_scan`; the next brick handles reaching the terminator.) -/
theorem gammaZeroScanProgram_runConfig_scanning {L maxIters : Nat} (x : Boolcube.Point L) :
    ∀ k : Nat, k ≤ maxIters →
      (∀ p : Fin ((gammaZeroScanProgram maxIters).toPhased.toTM.tapeLength L),
        (p : Nat) < k →
        ((gammaZeroScanProgram maxIters).toPhased.toTM.initialConfig x).tape p = false) →
      (((TM.runConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM)
          ((gammaZeroScanProgram maxIters).toPhased.toTM.initialConfig x) k).state).fst : Nat) = k
      ∧ ((TM.runConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM)
          ((gammaZeroScanProgram maxIters).toPhased.toTM.initialConfig x) k).state).snd = true
      ∧ ((TM.runConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM)
          ((gammaZeroScanProgram maxIters).toPhased.toTM.initialConfig x) k).head : Nat) = k
      ∧ (TM.runConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM)
          ((gammaZeroScanProgram maxIters).toPhased.toTM.initialConfig x) k).tape
          = ((gammaZeroScanProgram maxIters).toPhased.toTM.initialConfig x).tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih =>
      intro hk h0
      obtain ⟨hph, hsnd, hhd, htp⟩ := ih (by omega) (fun p hp => h0 p (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (gammaZeroScanProgram maxIters).toPhased.toTM)
        ((gammaZeroScanProgram maxIters).toPhased.toTM.initialConfig x) k with hc
      have hi : (c.state.fst : Nat) < maxIters := by rw [hph]; omega
      have hread : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega)
      have hcond : (c.state.snd && !(c.tape c.head)) = true := by simp [hsnd, hread]
      have hbnd : (c.head : Nat) + 1
          < (gammaZeroScanProgram maxIters).toPhased.toTM.tapeLength L := by
        rw [hhd]; show k + 1 < L + maxIters + 1; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [gammaZeroScanProgram_stepConfig_phase c (i := c.state.fst) (s := c.state.snd) hi rfl, hph]
      · rw [gammaZeroScanProgram_stepConfig_state c (i := c.state.fst) (s := c.state.snd) hi rfl]
        exact hcond
      · rw [gammaZeroScanProgram_stepConfig_head c (i := c.state.fst) (s := c.state.snd) hi rfl,
          hcond]
        simp only [cond_true, Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [gammaZeroScanProgram_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) hi rfl, htp]

end ContractExpansion
end Frontier
end Pnp4
