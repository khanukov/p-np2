import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

universe v
variable {S : Type v} [Fintype S] [DecidableEq S] [Inhabited S]

/-!
# Bounded loop for uniform-state phased programs

NP-verifier track (Phase 6 → 5/6): the missing control-flow primitive identified in
`TM_VERIFIER_STRATEGY.md`.

The Turing-machine model runs a program for a *fixed* number of steps (`runTime n`) and the toolkit's
`seq` / `seqList` are straight-line (no back-edges).  Iterating a body `k` times for a **symbolic** `k`
(e.g. `k = 2 ^ n`, the number of truth-table rows) is nonetheless expressible: `seqList` of
`List.replicate k body` is a well-typed `ConstStatePhasedProgram` for any `k : Nat`, and its
`timeBound` / run behaviour follow from the existing `seqList` recurrences by induction on `k`.  No new
back-edge machinery is needed — this is the verifier's row-iteration loop.
-/

/-- Run `body` sequentially `k` times (straight-line repetition, valid for symbolic `k`). -/
def repeatProgram (body : ConstStatePhasedProgram S) (k : Nat) : ConstStatePhasedProgram S :=
  seqList (List.replicate k body)

@[simp] theorem repeatProgram_zero (body : ConstStatePhasedProgram S) :
    repeatProgram body 0 = idleCS := rfl

/-- One iteration peels off the front (this is `rfl`, since `List.replicate (k+1)` is a cons). -/
theorem repeatProgram_succ (body : ConstStatePhasedProgram S) (k : Nat) :
    repeatProgram body (k + 1) = seq body (repeatProgram body k) := rfl

/-- Closed-form `timeBound`: `k` copies of the body plus one handoff per copy. -/
theorem repeatProgram_timeBound (body : ConstStatePhasedProgram S) (k n : Nat) :
    (repeatProgram body k).timeBound n = k * body.timeBound n + k := by
  induction k with
  | zero => simp [repeatProgram_zero]
  | succ k ih =>
      rw [repeatProgram_succ, seq_timeBound, ih]
      have hmul : (k + 1) * body.timeBound n = k * body.timeBound n + body.timeBound n :=
        Nat.succ_mul k (body.timeBound n)
      omega

/-- Uniform polynomial bound for the bounded loop: if the body runs within `B` steps, `k` iterations
run within `k * (B + 1)` steps.  This is the row loop's runtime-accounting shape — with `k = 2 ^ n`
and `B = poly n` it gives `2 ^ n * (poly n + 1) = poly L`, the form the eventual `runTime_poly`
obligation is discharged against. -/
theorem repeatProgram_timeBound_le (body : ConstStatePhasedProgram S) (k n B : Nat)
    (hB : body.timeBound n ≤ B) :
    (repeatProgram body k).timeBound n ≤ k * (B + 1) := by
  have hmul : k * body.timeBound n ≤ k * B := Nat.mul_le_mul (Nat.le_refl k) hB
  rw [repeatProgram_timeBound, Nat.mul_succ]
  omega

/--
Per-iteration run decomposition: running `repeatProgram body (k+1)` for its full `timeBound`
equals running the body once (its own `timeBound` steps) and then running the remaining `k` copies
(for `(repeatProgram body k).timeBound + 1` steps).  Inherited from `seqList_run_decomp`; this is the
inductive backbone for the eventual loop invariant.
-/
theorem repeatProgram_run_succ (body : ConstStatePhasedProgram S) (k : Nat) {n : Nat}
    (c : Configuration (M := (repeatProgram body (k + 1)).toPhased.toTM) n) :
    TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM) c
        ((repeatProgram body (k + 1)).timeBound n)
      = TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM)
          (TM.runConfig (M := (repeatProgram body (k + 1)).toPhased.toTM) c (body.timeBound n))
          ((repeatProgram body k).timeBound n + 1) := by
  simp only [repeatProgram, List.replicate_succ] at c ⊢
  exact seqList_run_decomp body (List.replicate k body) c

/-- Base case: zero iterations leave the configuration unchanged.  Together with
`repeatProgram_run_succ` this is the base/step pair for a loop invariant by induction on `k`. -/
theorem repeatProgram_run_zero (body : ConstStatePhasedProgram S) {n : Nat}
    (c : Configuration (M := (repeatProgram body 0).toPhased.toTM) n) :
    TM.runConfig (M := (repeatProgram body 0).toPhased.toTM) c
        ((repeatProgram body 0).timeBound n) = c := by
  have h0 : (repeatProgram body 0).timeBound n = 0 := by
    rw [repeatProgram_timeBound]; simp
  rw [h0]
  rfl

/--
General closed form for the `timeBound` of a sequential composition: the sum of the components'
time bounds plus one handoff per component.  The verifier TM is assembled as a `seqList` of phase
programs, so this is the shape its polynomial `runTime` bound is proved against (generalizing the
toolkit's explicit `seqList_timeBound_singleton`/`_two`/`_three`).
-/
theorem seqList_timeBound_sum (ps : List (ConstStatePhasedProgram S)) (n : Nat) :
    (seqList ps).timeBound n = (ps.map (fun p => p.timeBound n)).sum + ps.length := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
      rw [seqList_timeBound_cons, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/--
Uniform polynomial bound for a sequential composition: if every phase runs within `B` steps, the
whole `seqList` runs within `ps.length * (B + 1)` steps.  The verifier's `runTime_poly` obligation
instantiates this with `B` a polynomial bound common to its (constantly many) phases.
-/
theorem seqList_timeBound_le (ps : List (ConstStatePhasedProgram S)) (n B : Nat)
    (hB : ∀ p ∈ ps, p.timeBound n ≤ B) :
    (seqList ps).timeBound n ≤ ps.length * (B + 1) := by
  have hsum : ∀ (qs : List (ConstStatePhasedProgram S)),
      (∀ p ∈ qs, p.timeBound n ≤ B) →
      (qs.map (fun p => p.timeBound n)).sum ≤ qs.length * B := by
    intro qs
    induction qs with
    | nil => intro _; simp
    | cons p rest ih =>
        intro h
        have hp : p.timeBound n ≤ B := h p (List.mem_cons.mpr (Or.inl rfl))
        have hrest := ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))
        have e1 : (rest.length + 1) * B = rest.length * B + B := Nat.succ_mul rest.length B
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  have hs := hsum ps hB
  have e2 : ps.length * (B + 1) = ps.length * B + ps.length := Nat.mul_succ ps.length B
  rw [seqList_timeBound_sum]
  omega

/-!
## Compositional `TMNeverMovesLeft`

The assembled verifier is a `seqList` of phase programs, and head-position tracking (offsets staying
within `tapeLength`) relies on the machine never moving left.  Rather than re-prove `neverMovesLeft`
monolithically for each composed program, these lemmas thread it through `seq` / `seqList`: a
composition of right-only/stay programs is itself right-only/stay.  The compiled-TM step's move is
definitionally the transition's move, and the toolkit's `seq_transition_*_move` lemmas characterize
each region (P1-normal mirrors P1, the P1-accept handoff is `Move.stay`, P2-region mirrors P2).
-/

/-- Transition-level never-left for `seq`: if both components' transition functions never move left,
neither does `seq P1 P2`'s. -/
theorem seq_transition_neverLeft (P1 P2 : ConstStatePhasedProgram S)
    (hP1 : ∀ (i : Fin P1.numPhases) (q : S) (b : Bool), (P1.transition i q b).2.2.2 ≠ Move.left)
    (hP2 : ∀ (i : Fin P2.numPhases) (q : S) (b : Bool), (P2.transition i q b).2.2.2 ≠ Move.left)
    (i : Fin (seq P1 P2).numPhases) (q : S) (b : Bool) :
    ((seq P1 P2).transition i q b).2.2.2 ≠ Move.left := by
  by_cases h1 : i.val < P1.numPhases
  · by_cases hacc : i.val = P1.acceptPhase.val
    · rw [seq_transition_P1_accept_move P1 P2 h1 hacc q b]; simp
    · rw [seq_transition_P1_normal_move P1 P2 h1 hacc q b]; exact hP1 ⟨i.val, h1⟩ q b
  · have h2 : P1.numPhases ≤ i.val := Nat.le_of_not_lt h1
    have hiLt : i.val < P1.numPhases + P2.numPhases := i.isLt
    have hlt : i.val - P1.numPhases < P2.numPhases := by omega
    rw [seq_transition_P2_move P1 P2 h2 hlt q b]; exact hP2 ⟨i.val - P1.numPhases, hlt⟩ q b

/-- `seq` preserves `TMNeverMovesLeft` (lifts `seq_transition_neverLeft` through `toPhased`/`toTM`). -/
theorem seq_neverMovesLeft (P1 P2 : ConstStatePhasedProgram S)
    (hP1 : TMNeverMovesLeft (P1.toPhased.toTM))
    (hP2 : TMNeverMovesLeft (P2.toPhased.toTM)) :
    TMNeverMovesLeft ((seq P1 P2).toPhased.toTM) := by
  intro st b
  obtain ⟨i, q⟩ := st
  exact seq_transition_neverLeft P1 P2
    (fun i q b => hP1 ⟨i, q⟩ b) (fun i q b => hP2 ⟨i, q⟩ b) i q b

/-- The idle program never moves left (it always stays). -/
theorem idleCS_neverMovesLeft : TMNeverMovesLeft ((idleCS (S := S)).toPhased.toTM) := by
  intro st b
  obtain ⟨i, q⟩ := st
  show ((idleCS (S := S)).transition i q b).2.2.2 ≠ Move.left
  simp [idleCS]

/-- `seqList` preserves `TMNeverMovesLeft`: if every component is right-only/stay, so is their
sequential composition.  Induction on the list (`seq_neverMovesLeft` at each cons,
`idleCS_neverMovesLeft` at the base).  This is the head-bound-tracking ingredient for the assembled
verifier, which is a `seqList` of phase programs. -/
theorem seqList_neverMovesLeft (ps : List (ConstStatePhasedProgram S))
    (h : ∀ p ∈ ps, TMNeverMovesLeft (p.toPhased.toTM)) :
    TMNeverMovesLeft ((seqList ps).toPhased.toTM) := by
  induction ps with
  | nil => exact idleCS_neverMovesLeft
  | cons p rest ih =>
      rw [seqList_cons]
      exact seq_neverMovesLeft p (seqList rest)
        (h p (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq))))

end ConstStatePhasedProgram
end TM
end PsubsetPpoly
end Internal
end Pnp3
