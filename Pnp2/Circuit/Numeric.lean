import Pnp2.Circuit.EntropyCover
import Mathlib.Data.Nat.Log

noncomputable section

open Classical

namespace Boolcube
namespace Circuit

/-- Convenience abbreviation for the exponent appearing in the cover bound. -/
def powFamilyExponentBound (n c : ℕ) : ℕ :=
  3 * n + 11 * powFamilyEntropyBound n c + 2

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



/-- The exponent governing the size of the covering family grows at most like a
single monomial of degree `2c + 1`.  The constant `555` is a generous upper
bound obtained by comparing each contribution with the dominant power. -/
lemma powFamilyExponentBound_le_monomial {n c : ℕ} (hn : 1 ≤ n) :
    powFamilyExponentBound n c ≤ 555 * n ^ (2 * c + 1) := by
  classical
  have hpoly := powFamilyEntropyBound_le_polynomial (n := n) (c := c)
  have hexp_poly :
      powFamilyExponentBound n c ≤
        3 * n + 44 * n ^ (c + 1) + 176 * n ^ (2 * c) + 308 * n ^ c + 24 := by
    have hscaled := Nat.mul_le_mul_left 11 hpoly
    have hsum :
        3 * n + 11 * (4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 28 * n ^ c + 2) + 2
          = 3 * n + 44 * n ^ (c + 1) + 176 * n ^ (2 * c) + 308 * n ^ c + 24 := by
      ring
    simpa [powFamilyExponentBound, hsum]
      using add_le_add_left hscaled (3 * n)
  have hpow_mono : ∀ {a b : ℕ}, a ≤ b → n ^ a ≤ n ^ b :=
    fun h => Nat.pow_le_pow_of_le_left hn h
  have hpow_ge_one : 1 ≤ n ^ (2 * c) :=
    Nat.one_le_pow_of_one_le hn _
  have hle_self_pow : n ≤ n ^ (2 * c + 1) := by
    have := Nat.mul_le_mul_left n hpow_ge_one
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hterm₁ : 3 * n ≤ 3 * n ^ (2 * c + 1) :=
    Nat.mul_le_mul_left _ hle_self_pow
  have hterm₂ : 44 * n ^ (c + 1) ≤ 44 * n ^ (2 * c + 1) := by
    have hc : c + 1 ≤ 2 * c + 1 := by
      have : c ≤ 2 * c := by
        have := Nat.le_add_right c c
        simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      exact add_le_add this (le_of_eq rfl)
    exact Nat.mul_le_mul_left _ (hpow_mono (by simpa using hc))
  have hterm₃ : 176 * n ^ (2 * c) ≤ 176 * n ^ (2 * c + 1) := by
    exact Nat.mul_le_mul_left _ (hpow_mono (Nat.le_succ _))
  have hterm₄ : 308 * n ^ c ≤ 308 * n ^ (2 * c + 1) := by
    have hc : c ≤ 2 * c := by
      have := Nat.le_add_right c c
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    exact Nat.mul_le_mul_left _ (hpow_mono (le_trans hc (Nat.le_succ _)))
  have hterm₅ : 24 ≤ 24 * n ^ (2 * c + 1) := by
    have hpos : 1 ≤ n ^ (2 * c + 1) :=
      Nat.one_le_pow_of_one_le hn _
    simpa using Nat.mul_le_mul_left 24 hpos
  have hbounded :
      3 * n + 44 * n ^ (c + 1) + 176 * n ^ (2 * c) + 308 * n ^ c + 24
        ≤ 555 * n ^ (2 * c + 1) := by
    have hsum := add_le_add hterm₁
      (add_le_add hterm₂ (add_le_add hterm₃ (add_le_add hterm₄ hterm₅)))
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hsum
  exact hexp_poly.trans hbounded

end Circuit
end Boolcube
