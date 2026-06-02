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

end ContractExpansion
end Frontier
end Pnp4
