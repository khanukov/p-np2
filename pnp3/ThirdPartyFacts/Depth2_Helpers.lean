/-!
  pnp3/ThirdPartyFacts/Depth2_Helpers.lean

  Helper lemmas for Depth-2 constructive switching proofs.
  These lemmas bridge the gap between errU definitions and proof goals.

  **Key lemmas:**
  - errU_eq_zero_of_agree: If f x = coveredB S x for all x, then errU f S = 0
  - errU_eq_zero_iff: Characterization of when errU equals zero
-/
import Core.BooleanBasics

namespace Pnp3
namespace Core

variable {n : Nat}

/-! ### Error computation lemmas -/

/--
If a function f agrees with its covering on all points, then the error is zero.
This is the key lemma for proving exact representations (epsilon = 0).
-/
lemma errU_eq_zero_of_agree
    (f : BitVec n → Bool)
    (Rset : List (Subcube n))
    (h : ∀ x, f x = coveredB Rset x) :
    errU f Rset = 0 := by
  unfold errU
  -- Count of mismatches is 0
  have hmismatches : ((Finset.univ : Finset (BitVec n)).filter
      (fun x => f x ≠ coveredB Rset x)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    ext x
    simp
    intro hmem
    have heq := h x
    exact hmem heq
  simp [hmismatches]

/--
Error is zero iff the function agrees with its covering everywhere.
-/
lemma errU_eq_zero_iff
    (f : BitVec n → Bool)
    (Rset : List (Subcube n)) :
    errU f Rset = 0 ↔ ∀ x, f x = coveredB Rset x := by
  constructor
  · intro herr x
    -- Contrapositive: if they disagree somewhere, error > 0
    by_contra hdisagree
    unfold errU at herr
    have : ((Finset.univ : Finset (BitVec n)).filter
        (fun y => f y ≠ coveredB Rset y)).card > 0 := by
      apply Finset.card_pos.mpr
      use x
      simp [hdisagree]
    -- But this contradicts error = 0
    simp at herr
    have : ((Finset.univ : Finset (BitVec n)).filter
        (fun y => f y ≠ coveredB Rset y)).card = 0 := by
      have h := Nat.eq_zero_of_le_zero ?_
      · exact h
      · have : (0 : Q) ≤ 0 := by simp
        sorry  -- Need to show: division = 0 implies numerator = 0
    omega
  · exact errU_eq_zero_of_agree f Rset

/--
For a Boolean value b, b = (b == true) is always true.
-/
lemma bool_eq_beq_true (b : Bool) : b = (b == true) := by
  cases b <;> rfl

/--
For a Boolean value b, !b = (b == false) is always true.
-/
lemma bool_not_eq_beq_false (b : Bool) : !b = (b == false) := by
  cases b <;> rfl

end Core
end Pnp3
