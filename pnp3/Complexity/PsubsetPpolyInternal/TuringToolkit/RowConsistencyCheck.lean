import Complexity.PsubsetPpolyInternal.TuringToolkit.GateWrappers
import Complexity.PsubsetPpolyInternal.TuringToolkit.CombineAtOffset

/-!
# Milestone G: Row Consistency Check for MCSP Verifier

Given a concrete row index `i`, this module defines a CS-program that
checks whether the circuit output matches the partial truth table entry
at row `i`, AND-combined with the mask bit for row `i`, OR-accumulated
into a global invalid flag.

The four-step composition (via `seqList`):

1. `circuitEvaluatorCS gates Δrowbase Δscratch` — evaluate the straight-line
   circuit on the row input bits, writing gate outputs to the scratch region.
2. `combineAtOffsetCS (Δscratch + gates.length - 1) (Δvalue + i) Δtmp (· ≠ ·)` —
   XOR the circuit's final output (the top gate) with the claimed value `value[i]`,
   writing the mismatch bit to `Δtmp`.
3. `combineAtOffsetCS (Δmask + i) Δtmp Δtmp (· && ·)` — AND the mask bit for
   row `i` with the XOR result, in place at `Δtmp`; this is the per-row
   inconsistency flag (non-zero only when mask[i] = 1 and the circuit disagrees).
4. `combineAtOffsetCS Δtmp Δflag Δflag (· || ·)` — OR the per-row flag into
   the global invalid flag in place.

## Offset hierarchy (precondition chain)

```
Δrowbase + n                  ≤ Δscratch   (F.4 requirement: row input preserved)
Δscratch + gates.length       ≤ Δmask      (scratch does not collide with mask)
Δmask + 2^n                   ≤ Δvalue     (mask region [Δmask, Δmask + 2^n))
Δvalue + 2^n                  ≤ Δtmp       (value region [Δvalue, Δvalue + 2^n))
Δtmp                          ≤ Δflag
i                             < 2^n        (row index bound)
0                             < gates.length  (non-empty circuit)
```

## In-place writes

Steps 3 and 4 write to the same position they read.  The `combineAtOffsetCS`
phase layout at `CombineAtOffset.lean:19-27` reads `src2` at phase
`Δ2 + 1` and writes at phase `Δdst + 2`.  These are distinct phases
even when `Δ2 = Δdst`, so the original value of `src2` is captured in
the state before the write, making in-place writes safe.

## Row input writing

This module ASSUMES the row input (the `n` bits representing index `i`)
is already written at `[head + Δrowbase, head + Δrowbase + n)` before
this program runs.  The outer row-loop program (Milestone H) is
responsible for writing the binary representation of `i` to that
region before invoking this per-row check.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace RowConsistencyCheck

open Pnp3.Internal.PsubsetPpoly.TM
open ConstStatePhasedProgram
open CombineAtOffset
open GateEvalCS
open Encoding

/-- Row consistency check for a concrete row index `i`.  Composes four
CS programs via `seqList`: circuit evaluation, XOR with claimed value,
AND with mask, OR into global flag.  See module docstring for details. -/
def rowConsistencyCheckCSAt_row {n : Nat}
    (gates : List (SLGate n))
    (Δrowbase Δscratch Δmask Δvalue Δtmp Δflag : Nat)
    (hle_rs : Δrowbase + n ≤ Δscratch)
    (i : Nat)
    -- XOR step (2): read circuit output at Δscratch + gates.length - 1
    -- and value at Δvalue + i, write to Δtmp.
    (hle_xor_12 : Δscratch + gates.length - 1 ≤ Δvalue + i)
    (hle_xor_2d : Δvalue + i ≤ Δtmp)
    -- AND step (3): read mask at Δmask + i and Δtmp, write to Δtmp.
    (hle_and_12 : Δmask + i ≤ Δtmp)
    -- OR step (4): read Δtmp and Δflag, write to Δflag.
    (hle_or_12 : Δtmp ≤ Δflag) :
    ConstStatePhasedProgram (Bool × Bool) :=
  ConstStatePhasedProgram.seqList [
    circuitEvaluatorCS gates Δrowbase Δscratch hle_rs,
    combineAtOffsetCS (Δscratch + gates.length - 1) (Δvalue + i) Δtmp
      hle_xor_12 hle_xor_2d (fun a b => !(decide (a = b))),
    combineAtOffsetCS (Δmask + i) Δtmp Δtmp
      hle_and_12 (le_refl _) (fun a b => a && b),
    combineAtOffsetCS Δtmp Δflag Δflag
      hle_or_12 (le_refl _) (fun a b => a || b)
  ]

/-! ### Structural lemmas: `timeBound` closed form

The composition's `timeBound` is the sum of per-step `timeBound`s plus
three handoff steps (one per `seq` in the `seqList`).  Per-step bounds:
- Step 1 (circuit evaluator): `(circuitEvaluatorCS gates ...).timeBound N`
- Step 2 (XOR): `2 * Δtmp + 3` (writes to `Δtmp`).
- Step 3 (AND): `2 * Δtmp + 3` (writes to `Δtmp`, in place).
- Step 4 (OR): `2 * Δflag + 3` (writes to `Δflag`, in place). -/

theorem rowConsistencyCheckCSAt_row_timeBound {n : Nat}
    (gates : List (SLGate n))
    (Δrowbase Δscratch Δmask Δvalue Δtmp Δflag : Nat)
    (hle_rs : Δrowbase + n ≤ Δscratch) (i : Nat)
    (hle_xor_12 : Δscratch + gates.length - 1 ≤ Δvalue + i)
    (hle_xor_2d : Δvalue + i ≤ Δtmp)
    (hle_and_12 : Δmask + i ≤ Δtmp)
    (hle_or_12 : Δtmp ≤ Δflag) (N : Nat) :
    (rowConsistencyCheckCSAt_row gates Δrowbase Δscratch Δmask Δvalue Δtmp Δflag
        hle_rs i hle_xor_12 hle_xor_2d hle_and_12 hle_or_12).timeBound N =
      (circuitEvaluatorCS gates Δrowbase Δscratch hle_rs).timeBound N +
      ((2 * Δtmp + 3) + ((2 * Δtmp + 3) + ((2 * Δflag + 3) + 0 + 1) + 1) + 1) + 1 := by
  show (ConstStatePhasedProgram.seqList _).timeBound N = _
  -- Unfold the 4-element seqList step by step.
  simp only [ConstStatePhasedProgram.seqList,
    ConstStatePhasedProgram.seq_timeBound,
    combineAtOffsetCS_timeBound,
    ConstStatePhasedProgram.idleCS_timeBound]

/-- Simpler closed form: the composition runs in at most
`(circuit timeBound) + 6 * Δflag + 15` steps (using `Δtmp ≤ Δflag`). -/
theorem rowConsistencyCheckCSAt_row_timeBound_le {n : Nat}
    (gates : List (SLGate n))
    (Δrowbase Δscratch Δmask Δvalue Δtmp Δflag : Nat)
    (hle_rs : Δrowbase + n ≤ Δscratch) (i : Nat)
    (hle_xor_12 : Δscratch + gates.length - 1 ≤ Δvalue + i)
    (hle_xor_2d : Δvalue + i ≤ Δtmp)
    (hle_and_12 : Δmask + i ≤ Δtmp)
    (hle_or_12 : Δtmp ≤ Δflag) (N : Nat) :
    (rowConsistencyCheckCSAt_row gates Δrowbase Δscratch Δmask Δvalue Δtmp Δflag
        hle_rs i hle_xor_12 hle_xor_2d hle_and_12 hle_or_12).timeBound N ≤
      (circuitEvaluatorCS gates Δrowbase Δscratch hle_rs).timeBound N +
      (6 * Δflag + 15) := by
  rw [rowConsistencyCheckCSAt_row_timeBound]
  -- Δtmp ≤ Δflag, so 2 * Δtmp + 3 ≤ 2 * Δflag + 3.
  have hΔ : Δtmp ≤ Δflag := hle_or_12
  omega

/-! ### Tape-outside preservation

The composition only modifies tape cells within
`[head + Δscratch, head + Δscratch + gates.length) ∪ {head + Δtmp, head + Δflag}`.
Any cell outside this region is preserved by a run of length
`timeBound`.  This invariant is needed for the outer row-loop
(Milestone H) to ensure that scratch from row `i` does not corrupt
data used by row `i + 1`.

Proof will be delivered in a follow-up session when the per-row
semantic correctness is established. -/

/-! ### `mcspCheckAllRows` — Path 1 loop-unroll via `List.ofFn`

Composes `rowConsistencyCheckCSAt_row` for each row `i : Fin (2 ^ n)`
via a single `seqList` built by `List.ofFn`.  Because each per-row
check has fixed (row-dependent) offsets, the total program is a
`PhasedProgram` with concrete `numPhases = 2^n · (per-row numPhases)`.
No foundation change to `PhasedProgram` is needed — see session 53
design note.

Note: the outer row-loop would normally also write the binary
representation of `i` into `[Δrowbase, Δrowbase + n)` before running
the per-row check.  That row-input write is a separate responsibility
deferred to Milestone H's row-loop compound.  Downstream users compose
`mcspCheckAllRows` with a preceding row-input writer for each `i`. -/

/-- Path 1 loop-unrolled MCSP-verifier core: applies
`rowConsistencyCheckCSAt_row` for each `i : Fin (2 ^ n)`.  The list
`List.ofFn (fun i => rowConsistencyCheckCSAt_row ... i.val ...)` is a
`Fin (2 ^ n)`-indexed list; `seqList` threads them sequentially.

Preconditions are packaged as universal: the caller provides a row-wise
constraint family `hrow : ∀ i : Fin (2 ^ n), ...`, which the definition
`List.ofFn` consumes at each index. -/
def mcspCheckAllRows {n : Nat}
    (gates : List (SLGate n))
    (Δrowbase Δscratch Δmask Δvalue Δtmp Δflag : Nat)
    (hle_rs : Δrowbase + n ≤ Δscratch)
    (hle_xor_12 : ∀ i : Fin (2 ^ n),
      Δscratch + gates.length - 1 ≤ Δvalue + i.val)
    (hle_xor_2d : ∀ i : Fin (2 ^ n), Δvalue + i.val ≤ Δtmp)
    (hle_and_12 : ∀ i : Fin (2 ^ n), Δmask + i.val ≤ Δtmp)
    (hle_or_12 : Δtmp ≤ Δflag) :
    ConstStatePhasedProgram (Bool × Bool) :=
  ConstStatePhasedProgram.seqList
    (List.ofFn (fun i : Fin (2 ^ n) =>
      rowConsistencyCheckCSAt_row gates Δrowbase Δscratch Δmask Δvalue Δtmp Δflag
        hle_rs i.val (hle_xor_12 i) (hle_xor_2d i) (hle_and_12 i) hle_or_12))

/-- Uniform bound on each per-row `timeBound`.  Each row runs in at
most `(circuit timeBound) + 6 * Δflag + 15` steps. -/
theorem mcspCheckAllRows_per_row_timeBound_le {n : Nat}
    (gates : List (SLGate n))
    (Δrowbase Δscratch Δmask Δvalue Δtmp Δflag : Nat)
    (hle_rs : Δrowbase + n ≤ Δscratch)
    (hle_xor_12 : ∀ i : Fin (2 ^ n),
      Δscratch + gates.length - 1 ≤ Δvalue + i.val)
    (hle_xor_2d : ∀ i : Fin (2 ^ n), Δvalue + i.val ≤ Δtmp)
    (hle_and_12 : ∀ i : Fin (2 ^ n), Δmask + i.val ≤ Δtmp)
    (hle_or_12 : Δtmp ≤ Δflag) (N : Nat)
    (i : Fin (2 ^ n)) :
    (rowConsistencyCheckCSAt_row gates Δrowbase Δscratch Δmask Δvalue Δtmp Δflag
        hle_rs i.val (hle_xor_12 i) (hle_xor_2d i) (hle_and_12 i) hle_or_12).timeBound N ≤
      (circuitEvaluatorCS gates Δrowbase Δscratch hle_rs).timeBound N +
      (6 * Δflag + 15) :=
  rowConsistencyCheckCSAt_row_timeBound_le _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Aggregate timeBound for `mcspCheckAllRows`: at most
`2^n · (circuit_tb + 6 * Δflag + 16) + 1` steps.

Uses `seqList_timeBound_le_uniform` with uniform per-row bound
`B = circuit_tb + 6 * Δflag + 15`, giving `2^n · (B + 1) + 1`. -/
theorem mcspCheckAllRows_timeBound_le {n : Nat}
    (gates : List (SLGate n))
    (Δrowbase Δscratch Δmask Δvalue Δtmp Δflag : Nat)
    (hle_rs : Δrowbase + n ≤ Δscratch)
    (hle_xor_12 : ∀ i : Fin (2 ^ n),
      Δscratch + gates.length - 1 ≤ Δvalue + i.val)
    (hle_xor_2d : ∀ i : Fin (2 ^ n), Δvalue + i.val ≤ Δtmp)
    (hle_and_12 : ∀ i : Fin (2 ^ n), Δmask + i.val ≤ Δtmp)
    (hle_or_12 : Δtmp ≤ Δflag) (N : Nat) :
    (mcspCheckAllRows gates Δrowbase Δscratch Δmask Δvalue Δtmp Δflag
        hle_rs hle_xor_12 hle_xor_2d hle_and_12 hle_or_12).timeBound N ≤
      2 ^ n * ((circuitEvaluatorCS gates Δrowbase Δscratch hle_rs).timeBound N +
                6 * Δflag + 16) + 1 := by
  -- Apply the generic `seqList_timeBound_le_uniform` with uniform
  -- bound B = (circuit timeBound N) + 6 * Δflag + 15.
  show (ConstStatePhasedProgram.seqList _).timeBound N ≤ _
  set B := (circuitEvaluatorCS gates Δrowbase Δscratch hle_rs).timeBound N +
             (6 * Δflag + 15) with hB_def
  have hlist_len : (List.ofFn (n := 2 ^ n)
      (fun i : Fin (2 ^ n) =>
        rowConsistencyCheckCSAt_row gates Δrowbase Δscratch Δmask Δvalue Δtmp Δflag
          hle_rs i.val (hle_xor_12 i) (hle_xor_2d i) (hle_and_12 i) hle_or_12)).length
      = 2 ^ n := by simp
  have h_each :
      ∀ p ∈ List.ofFn (n := 2 ^ n)
        (fun i : Fin (2 ^ n) =>
          rowConsistencyCheckCSAt_row gates Δrowbase Δscratch Δmask Δvalue Δtmp Δflag
            hle_rs i.val (hle_xor_12 i) (hle_xor_2d i) (hle_and_12 i) hle_or_12),
        p.timeBound N ≤ B := by
    intro p hp
    rcases List.mem_ofFn.mp hp with ⟨i, hi⟩
    rw [← hi]
    exact rowConsistencyCheckCSAt_row_timeBound_le _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have huni := seqList_timeBound_le_uniform _ B N h_each
  rw [hlist_len] at huni
  -- Finish: `2^n * (B + 1) + 1 = 2^n * (circuit_tb + 6 * Δflag + 16) + 1`.
  have h_eq : B + 1 =
      (circuitEvaluatorCS gates Δrowbase Δscratch hle_rs).timeBound N +
        6 * Δflag + 16 := by
    show _ = _
    omega
  calc (ConstStatePhasedProgram.seqList _).timeBound N
      ≤ 2 ^ n * (B + 1) + 1 := huni
    _ = 2 ^ n * ((circuitEvaluatorCS gates Δrowbase Δscratch hle_rs).timeBound N +
                 6 * Δflag + 16) + 1 := by rw [h_eq]

end RowConsistencyCheck

end TM
end PsubsetPpoly
end Internal
end Pnp3
