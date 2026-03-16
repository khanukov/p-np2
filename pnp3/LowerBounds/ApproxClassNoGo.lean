import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import LowerBounds.ApproxClassContradiction

/-!
  pnp3/LowerBounds/ApproxClassNoGo.lean

  Formal insufficiency results for the current singleton `ApproxClass` layer.

  The point is negative but precise: belonging to `ApproxClass` with some error
  parameter does not, by itself, force existence of a bounded witness whose
  mismatch set is small in cardinality.
-/

namespace Pnp3
namespace LowerBounds

open Counting
open Core

/-- Indicator of a finite set as a Boolean function. -/
private def indicatorOfFinset {m : Nat}
    (T : Finset (Counting.Domain m)) : Counting.Domain m → Bool :=
  fun x => decide (x ∈ T)

/-- Against the constant-false approximant, the mismatch set is exactly `T`. -/
lemma mismatchSet_false_indicator_eq {m : Nat}
    (T : Finset (Counting.Domain m)) :
    Counting.mismatchSet (fun _ => false) (indicatorOfFinset T) = T := by
  classical
  ext x
  simp [Counting.mismatchSet, indicatorOfFinset]

/--
`ApproxClass` alone does not force a witness with small mismatch-cardinality.

The counterexample uses the empty dictionary and a function supported on
exactly `B + 1` inputs.
-/
theorem approxClass_does_not_imply_small_mismatch
    {m B : Nat} (hB : B < 2 ^ m) :
    ∃ (R : List (Core.Subcube m)) (k : Nat) (ε : Core.Q)
      (f : Core.BitVec m → Bool),
      f ∈ Counting.ApproxClass (R := R) (k := k) (ε := ε) ∧
      ¬ ∃ S : List (Core.Subcube m),
          S.length ≤ k ∧
          Core.listSubset S R ∧
          (Counting.mismatchSet (fun x => Core.coveredB S x) f).card ≤ B := by
  classical
  let α := Counting.Domain m
  have hcardDomain : Fintype.card α = 2 ^ m := by
    simp [α, Counting.Domain, Core.BitVec, Fintype.card_bool, Fintype.card_fin]
  have hBsucc : B + 1 ≤ 2 ^ m := Nat.succ_le_of_lt hB
  have hBsucc' : B + 1 ≤ Fintype.card α := by
    simpa [hcardDomain] using hBsucc
  obtain ⟨T, _hEmpty, hTcard⟩ :=
    Finset.exists_superset_card_eq (s := (∅ : Finset α)) (n := B + 1)
      (by simp) hBsucc'
  let f : Core.BitVec m → Bool := indicatorOfFinset T
  let ε : Core.Q := ((T.card : Nat) : Core.Q) / ((2 ^ m : Nat) : Core.Q)
  refine ⟨[], 0, ε, f, ?_, ?_⟩
  · have herr : Core.errU f ([] : List (Core.Subcube m)) ≤ ε := by
      rw [Core.errU_nil_eq_yes_density]
      simp [f, indicatorOfFinset, ε, hTcard]
    exact
      Counting.approx_mem_of_errU_le
        (R := [])
        (k := 0)
        (ε := ε)
        (f := f)
        ⟨[], by simp, Core.listSubset_nil [], herr⟩
  · intro hsmall
    rcases hsmall with ⟨S, hlen, _hsub, hcard⟩
    have hS : S = [] := by
      have hlen0 : S.length = 0 := by omega
      simpa using hlen0
    have hmis : Counting.mismatchSet (fun x => Core.coveredB S x) f = T := by
      subst hS
      simpa [f, indicatorOfFinset] using
        mismatchSet_false_indicator_eq (m := m) T
    have hTle : T.card ≤ B := by
      simpa [hmis] using hcard
    have : B + 1 ≤ B := by
      simpa [hTcard] using hTle
    omega

end LowerBounds
end Pnp3
