import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Counting.CircuitCounting
import Counting.ShannonCounting
import Models.Model_PartialMCSP

namespace Pnp3
namespace LowerBounds

open Core
open Models
open Counting

/-!
# Trace-set / sparse anti-checker local bricks

This file is an audit-oriented sandbox for the Trace-Set route.
It intentionally proves only local combinatorial lemmas and does NOT claim
an unconditional NP-vs-P/poly separation.
-/

/-- Row-trace of a circuit on a finite family of sampled rows. -/
def traceCircuitOnRows {n m : Nat}
    (rows : Fin m → Core.BitVec n)
    (C : Models.Circuit n) : Core.BitVec m :=
  fun j => Models.Circuit.eval C (rows j)

/-- Image of all traces induced by circuits of size at most `s`. -/
noncomputable def traceImage
    (n s m : Nat)
    (rows : Fin m → Core.BitVec n) :
    Finset (Core.BitVec m) :=
  (Counting.circuitsOfSizeAtMost n s).image
    (fun C => traceCircuitOnRows rows C)

/-- Cardinality of the trace image is at most the circuit counting envelope. -/
theorem traceImage_card_le
    (n s m : Nat)
    (rows : Fin m → Core.BitVec n) :
    (traceImage n s m rows).card ≤ Models.circuitCountBound n s := by
  classical
  calc
    (traceImage n s m rows).card
        ≤ (Counting.circuitsOfSizeAtMost n s).card := by
          exact Finset.card_image_le
    _ ≤ Models.circuitCountBound n s := by
          exact Counting.card_circuitsOfSizeAtMost_le n s

/-- Finite pigeonhole helper: a strict-cardinality gap yields a missing point. -/
theorem exists_not_mem_finset_of_card_lt
    {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset α)
    (h : A.card < Fintype.card α) :
    ∃ x : α, x ∉ A := by
  classical
  by_contra hAll
  push_neg at hAll
  have hEq : A = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    exact hAll x
  rw [hEq] at h
  simp at h

/-- If counting slack beats `2^m`, there exists an unrealized trace label. -/
theorem exists_unrealized_trace
    {n s m : Nat}
    (rows : Fin m → Core.BitVec n)
    (hSlack : Models.circuitCountBound n s < 2 ^ m) :
    ∃ y : Core.BitVec m,
      y ∉ traceImage n s m rows := by
  classical
  have hCard :
      (traceImage n s m rows).card <
        Fintype.card (Core.BitVec m) := by
    calc
      (traceImage n s m rows).card
          ≤ Models.circuitCountBound n s :=
            traceImage_card_le n s m rows
      _ < 2 ^ m := hSlack
      _ = Fintype.card (Core.BitVec m) := by
            simp
  exact exists_not_mem_finset_of_card_lt
    (traceImage n s m rows) hCard

/-- Build a partial table by assigning `rows[j] ↦ y[j]` and leaving other points undefined. -/
noncomputable def partialFromTrace
    {n m : Nat}
    (rows : Fin m → Core.BitVec n)
    (y : Core.BitVec m) :
    Models.PartialTruthTable n :=
  fun i =>
    if h : ∃ j : Fin m, Models.assignmentIndex (rows j) = i then
      some (y (Classical.choose h))
    else
      none

/-- On sampled rows, `partialFromTrace` returns the intended bit label. -/
theorem partialFromTrace_at_row
    {n m : Nat}
    (rows : Fin m → Core.BitVec n)
    (rowsInj :
      Function.Injective
        (fun j : Fin m => Models.assignmentIndex (rows j)))
    (y : Core.BitVec m)
    (j : Fin m) :
    partialFromTrace rows y
      (Models.assignmentIndex (rows j)) = some (y j) := by
  classical
  unfold partialFromTrace
  have hExists :
      ∃ k : Fin m,
        Models.assignmentIndex (rows k) =
          Models.assignmentIndex (rows j) := ⟨j, rfl⟩
  rw [dif_pos hExists]
  have hChoose :
      Models.assignmentIndex
        (rows (Classical.choose hExists)) =
      Models.assignmentIndex (rows j) :=
    Classical.choose_spec hExists
  have hEq :
      Classical.choose hExists = j :=
    rowsInj hChoose
  rw [hEq]

end LowerBounds
end Pnp3
