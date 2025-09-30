import Pnp2.Circuit.EntropyCover
import Mathlib.Data.Nat.Log

noncomputable section

open Classical

namespace Boolcube
namespace Circuit

/-- A coarse but explicit upper bound on `powFamilyEntropyBound`.  The bound is
obtained by replacing each logarithm by its argument and by bounding the
auxiliary alphabet size `encodingAlphabet` with the naive sum `n + 4 * n^c + 5`.
Although extremely loose, the estimate suffices for later comparisons with the
ambient power `2^n`. -/
lemma powFamilyEntropyBound_le_polynomial (n c : ℕ) :
    powFamilyEntropyBound n c ≤
      4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 28 * n ^ c + 2 := by
  classical
  -- Abbreviations for clarity.
  set L := encodingLength n c := 4 * n ^ c
  set A := encodingAlphabet n c := max n (4 * n ^ c) + 5
  -- Replace integer logarithms by their arguments.
  have hlog₁ : Nat.log2 (L + 1) ≤ L + 1 := by
    simpa [Nat.log2_eq_log_two] using (Nat.log_le_self (2) (L + 1))
  have hlog₂ : Nat.log2 A ≤ A := by
    simpa [Nat.log2_eq_log_two] using (Nat.log_le_self (2) A)
  -- From the definition of `powFamilyEntropyBound` we obtain a linear bound in
  -- terms of `L` and `A`.
  have hstep :
      powFamilyEntropyBound n c ≤ L * A + 2 * L + 2 := by
    have := add_le_add
      (add_le_add_right hlog₁ 1)
      (Nat.mul_le_mul_left _ (add_le_add_right hlog₂ 1))
    simpa [powFamilyEntropyBound, L, A, encodingLength, encodingAlphabet,
      Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc, Nat.add_mul, two_mul] using this
  -- Crude inequality for the alphabet size.
  have hA_le : A ≤ n + 4 * n ^ c + 5 := by
    refine Nat.add_le_add_right ?_ 5
    exact max_le
      (Nat.le_add_right _ _)
      (Nat.le_add_left _ _)
  -- Bounding the product term `L * A`.
  have hprod : L * A ≤ 4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 20 * n ^ c := by
    have := Nat.mul_le_mul_left L hA_le
    simpa [L, encodingLength, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.pow_add, Nat.pow_succ, Nat.succ_eq_add_one] using this
  -- Bounding the remaining linear term.
  have hlin : 2 * L ≤ 8 * n ^ c := by
    simp [L, encodingLength, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  -- Combine the pieces and regroup constants.
  have htotal : L * A + 2 * L + 2 ≤
      (4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 20 * n ^ c) + 8 * n ^ c + 2 := by
    have := add_le_add hprod hlin
    exact add_le_add_right this 2
  have htarget :
      (4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 20 * n ^ c) + 8 * n ^ c + 2
        = 4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 28 * n ^ c + 2 := by
    ring
  exact hstep.trans (by simpa [htarget] using htotal)

end Circuit
end Boolcube
