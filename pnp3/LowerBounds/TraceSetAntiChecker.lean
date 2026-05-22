import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Counting.CircuitCounting
import Models.Model_PartialMCSP

namespace Pnp3
namespace LowerBounds

open Core
open Models
open Counting

/-!
# Trace-set / sparse anti-checker local bricks

This module is a **local audit surface** for the Trace-Set route.
It proves row-trace counting and consistency lemmas without claiming
an unconditional endpoint.

Key design choice:
- we expose both an **over-approximate envelope image** (over all
  enumerated circuits) and an **exact filtered image** (only circuits
  with syntactic size bound).
-/

/-- Row-trace of a circuit on sampled rows. -/
def traceCircuitOnRows {n m : Nat}
    (rows : Fin m → Core.BitVec n)
    (C : Models.Circuit n) : Core.BitVec m :=
  fun j => Models.Circuit.eval C (rows j)

/-- Envelope image: traces of the whole enumeration `circuitsOfSizeAtMost`. -/
noncomputable def traceImageEnvelope
    (n s m : Nat)
    (rows : Fin m → Core.BitVec n) :
    Finset (Core.BitVec m) :=
  (Counting.circuitsOfSizeAtMost n s).image
    (fun C => traceCircuitOnRows rows C)

/-- Exact small-circuit set extracted from the envelope enumeration. -/
noncomputable def smallCircuitsExact (n s : Nat) : Finset (Models.Circuit n) :=
  (Counting.circuitsOfSizeAtMost n s).filter (fun C => C.size ≤ s)

/-- Exact trace image: only traces of circuits with `size ≤ s`. -/
noncomputable def traceImageExact
    (n s m : Nat)
    (rows : Fin m → Core.BitVec n) :
    Finset (Core.BitVec m) :=
  (smallCircuitsExact n s).image
    (fun C => traceCircuitOnRows rows C)

/-- Characterization of membership in the exact small-circuit carrier. -/
theorem mem_smallCircuitsExact_iff
    {n s : Nat} {C : Models.Circuit n} :
    C ∈ smallCircuitsExact n s ↔ C ∈ Counting.circuitsOfSizeAtMost n s ∧ C.size ≤ s := by
  simp [smallCircuitsExact]

/-- Exact carrier is a subset of the envelope carrier. -/
theorem smallCircuitsExact_subset (n s : Nat) :
    smallCircuitsExact n s ⊆ Counting.circuitsOfSizeAtMost n s := by
  intro C hC
  exact (mem_smallCircuitsExact_iff.mp hC).1

/-- Exact trace image is a subset of the envelope trace image. -/
theorem traceImageExact_subset_traceImageEnvelope
    (n s m : Nat)
    (rows : Fin m → Core.BitVec n) :
    traceImageExact n s m rows ⊆ traceImageEnvelope n s m rows := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨C, hC, rfl⟩
  exact Finset.mem_image.mpr ⟨C, smallCircuitsExact_subset n s hC, rfl⟩

/-- Envelope cardinality bound via existing circuit counting envelope. -/
theorem traceImageEnvelope_card_le
    (n s m : Nat)
    (rows : Fin m → Core.BitVec n) :
    (traceImageEnvelope n s m rows).card ≤ Models.circuitCountBound n s := by
  classical
  calc
    (traceImageEnvelope n s m rows).card
        ≤ (Counting.circuitsOfSizeAtMost n s).card := by
          exact Finset.card_image_le
    _ ≤ Models.circuitCountBound n s := by
          exact Counting.card_circuitsOfSizeAtMost_le n s

/-- Exact cardinality bound (as a corollary of the envelope bound). -/
theorem traceImageExact_card_le
    (n s m : Nat)
    (rows : Fin m → Core.BitVec n) :
    (traceImageExact n s m rows).card ≤ Models.circuitCountBound n s := by
  have hSub := traceImageExact_subset_traceImageEnvelope n s m rows
  exact le_trans (Finset.card_le_card hSub) (traceImageEnvelope_card_le n s m rows)

/-- Finite pigeonhole helper. -/
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

/-- Envelope version: strict counting slack yields an unrealized trace. -/
theorem exists_unrealized_trace_envelope
    {n s m : Nat}
    (rows : Fin m → Core.BitVec n)
    (hSlack : Models.circuitCountBound n s < 2 ^ m) :
    ∃ y : Core.BitVec m,
      y ∉ traceImageEnvelope n s m rows := by
  classical
  have hCard :
      (traceImageEnvelope n s m rows).card <
        Fintype.card (Core.BitVec m) := by
    calc
      (traceImageEnvelope n s m rows).card
          ≤ Models.circuitCountBound n s :=
            traceImageEnvelope_card_le n s m rows
      _ < 2 ^ m := hSlack
      _ = Fintype.card (Core.BitVec m) := by
            simp
  exact exists_not_mem_finset_of_card_lt
    (traceImageEnvelope n s m rows) hCard

/-- Exact version: strict counting slack yields an unrealized exact trace. -/
theorem exists_unrealized_trace_exact
    {n s m : Nat}
    (rows : Fin m → Core.BitVec n)
    (hSlack : Models.circuitCountBound n s < 2 ^ m) :
    ∃ y : Core.BitVec m,
      y ∉ traceImageExact n s m rows := by
  classical
  have hCard :
      (traceImageExact n s m rows).card <
        Fintype.card (Core.BitVec m) := by
    calc
      (traceImageExact n s m rows).card
          ≤ Models.circuitCountBound n s :=
            traceImageExact_card_le n s m rows
      _ < 2 ^ m := hSlack
      _ = Fintype.card (Core.BitVec m) := by
            simp
  exact exists_not_mem_finset_of_card_lt
    (traceImageExact n s m rows) hCard

/-- `assignmentIndex` is injective (already derivable from round-trip lemmas). -/
theorem assignmentIndex_injective {n : Nat} :
    Function.Injective (@Models.assignmentIndex n) := by
  intro x y hxy
  have hx := Models.vecOfNat_assignmentIndex_val x
  have hy := Models.vecOfNat_assignmentIndex_val y
  rw [hxy] at hx
  exact hx.symm.trans hy

/-- Build a partial table from row labels, leaving all other points undefined. -/
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

/-- Lookup on a sampled row returns the designated label. -/
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

/-- Consistency with `partialFromTrace` forces trace equality. -/
theorem trace_eq_of_consistent_partialFromTrace
    {n m : Nat}
    (rows : Fin m → Core.BitVec n)
    (rowsInj :
      Function.Injective
        (fun j : Fin m => Models.assignmentIndex (rows j)))
    (y : Core.BitVec m)
    (C : Models.Circuit n)
    (hCons :
      Models.is_consistent C (partialFromTrace rows y)) :
    traceCircuitOnRows rows C = y := by
  funext j
  have hAt := hCons (rows j)
  have hLookup := partialFromTrace_at_row rows rowsInj y j
  simpa [Models.is_consistent, traceCircuitOnRows, hLookup] using hAt

/-- Reverse direction: exact row-trace equality implies consistency. -/
theorem consistent_partialFromTrace_of_trace_eq
    {n m : Nat}
    (rows : Fin m → Core.BitVec n)
    (y : Core.BitVec m)
    (C : Models.Circuit n)
    (hTrace : traceCircuitOnRows rows C = y) :
    Models.is_consistent C (partialFromTrace rows y) := by
  intro x
  by_cases hMem : ∃ j : Fin m, Models.assignmentIndex (rows j) = Models.assignmentIndex x
  · have hEqJ : rows (Classical.choose hMem) = x := by
      apply assignmentIndex_injective
      exact Classical.choose_spec hMem
    have hAt :
        partialFromTrace rows y (Models.assignmentIndex x) =
          some (y (Classical.choose hMem)) := by
      unfold partialFromTrace
      rw [dif_pos hMem]
    rw [hAt]
    have hTraceAt := congrArg (fun f => f (Classical.choose hMem)) hTrace
    simpa [traceCircuitOnRows, hEqJ] using hTraceAt
  · unfold partialFromTrace
    rw [dif_neg hMem]
    trivial

/-- Sparse anti-checker local NO lemma from unrealized exact trace. -/
theorem partialFromTrace_NO_of_unrealized
    {p : Models.GapPartialMCSPParams}
    {m : Nat}
    (rows : Fin m → Core.BitVec p.n)
    (rowsInj :
      Function.Injective
        (fun j : Fin m => Models.assignmentIndex (rows j)))
    (y : Core.BitVec m)
    (hy :
      y ∉ traceImageExact p.n (p.sNO - 1) m rows) :
    Models.PartialMCSP_NO p (partialFromTrace rows y) := by
  intro C hCons
  by_contra hSmallFail
  have hSmall : C.size ≤ p.sNO - 1 := by omega
  have hMemSmall : C ∈ smallCircuitsExact p.n (p.sNO - 1) := by
    refine (mem_smallCircuitsExact_iff).2 ?_
    exact ⟨Counting.mem_circuitsOfSizeAtMost C (p.sNO - 1) hSmall, hSmall⟩
  have hTraceEq : traceCircuitOnRows rows C = y :=
    trace_eq_of_consistent_partialFromTrace rows rowsInj y C hCons
  have hMemTrace : y ∈ traceImageExact p.n (p.sNO - 1) m rows := by
    exact Finset.mem_image.mpr ⟨C, hMemSmall, hTraceEq⟩
  exact hy hMemTrace

/-- Exact YES characterization for partial tables produced from traces. -/
theorem PartialMCSP_YES_iff_mem_traceImageExact
    {p : Models.GapPartialMCSPParams}
    {m : Nat}
    (rows : Fin m → Core.BitVec p.n)
    (rowsInj :
      Function.Injective
        (fun j : Fin m => Models.assignmentIndex (rows j)))
    (y : Core.BitVec m) :
    Models.PartialMCSP_YES p (partialFromTrace rows y) ↔
      y ∈ traceImageExact p.n p.sYES m rows := by
  constructor
  · intro hYes
    rcases hYes with ⟨C, hSize, hCons⟩
    have hMemSmall : C ∈ smallCircuitsExact p.n p.sYES := by
      refine (mem_smallCircuitsExact_iff).2 ?_
      exact ⟨Counting.mem_circuitsOfSizeAtMost C p.sYES hSize, hSize⟩
    have hTraceEq : traceCircuitOnRows rows C = y :=
      trace_eq_of_consistent_partialFromTrace rows rowsInj y C hCons
    exact Finset.mem_image.mpr ⟨C, hMemSmall, hTraceEq⟩
  · intro hMem
    rcases Finset.mem_image.mp hMem with ⟨C, hC, hTrace⟩
    have hSmall : C.size ≤ p.sYES := (mem_smallCircuitsExact_iff.mp hC).2
    refine ⟨C, hSmall, ?_⟩
    exact consistent_partialFromTrace_of_trace_eq rows y C hTrace

/-- Language-level bridge for encoded `partialFromTrace`. -/
theorem gapPartialMCSP_trace_yes_iff
    {p : Models.GapPartialMCSPParams}
    {m : Nat}
    (rows : Fin m → Core.BitVec p.n)
    (rowsInj :
      Function.Injective
        (fun j : Fin m => Models.assignmentIndex (rows j)))
    (y : Core.BitVec m) :
    Models.gapPartialMCSP_Language p
      (Models.partialInputLen p)
      (Models.encodePartial (partialFromTrace rows y)) = true
    ↔
    y ∈ traceImageExact p.n p.sYES m rows := by
  have hYes :
      Models.gapPartialMCSP_Language p
        (Models.partialInputLen p)
        (Models.encodePartial (partialFromTrace rows y)) = true
      ↔
      Models.PartialMCSP_YES p
        (Models.decodePartial (Models.encodePartial (partialFromTrace rows y))) :=
    Models.gapPartialMCSP_language_true_iff_yes p
      (Models.encodePartial (partialFromTrace rows y))
  rw [hYes, Models.decodePartial_encodePartial]
  exact PartialMCSP_YES_iff_mem_traceImageExact rows rowsInj y

/-- Unrealized exact trace at NO-threshold implies language value `false`. -/
theorem gapPartialMCSP_trace_false_of_unrealized_NO
    {p : Models.GapPartialMCSPParams}
    {m : Nat}
    (rows : Fin m → Core.BitVec p.n)
    (rowsInj :
      Function.Injective
        (fun j : Fin m => Models.assignmentIndex (rows j)))
    (y : Core.BitVec m)
    (hy :
      y ∉ traceImageExact p.n (p.sNO - 1) m rows) :
    Models.gapPartialMCSP_Language p
      (Models.partialInputLen p)
      (Models.encodePartial (partialFromTrace rows y)) = false := by
  have hNO := partialFromTrace_NO_of_unrealized rows rowsInj y hy
  exact Models.gapPartialMCSP_language_false_of_no p
    (Models.encodePartial (partialFromTrace rows y))
    (by simpa [Models.decodePartial_encodePartial] using hNO)

end LowerBounds
end Pnp3
