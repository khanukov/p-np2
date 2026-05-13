import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.BitIndices

/-!
# Power-of-two slice width helpers

This module supplies the Tier-1.B arithmetic facts for the log-width
hardwiring lift seed pack.  The width function is deliberately sparse:
it returns the binary exponent on exact powers of two and `0` elsewhere.
That is enough for the downstream power-of-two-slice adversary: the selected
window is always within the ambient input length, becomes arbitrarily large on
powers of two, and is strictly below the ambient length infinitely often.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

/-- Sparse log-width selector for power-of-two lengths.

At lengths `n = 2^t`, this is exactly `t`; at lengths that are not equal to
`2 ^ Nat.log 2 n`, it is `0`.  Testing the canonical logarithmic candidate
keeps the definition decidable while preserving the exact power-of-two slices
needed downstream. -/
def k_pow2 (n : Nat) : Nat :=
  if n = 2 ^ Nat.log 2 n then Nat.log 2 n else 0

/-- Elementary exponential domination used to show `k_pow2 n ≤ n` on slices. -/
theorem lt_two_pow_self (t : Nat) : t < 2 ^ t :=
  (show t < 2 ^ t from Nat.lt_two_pow_self)

/-- Weak form of `lt_two_pow_self`. -/
theorem le_two_pow_self (t : Nat) : t ≤ 2 ^ t :=
  Nat.le_of_lt (lt_two_pow_self t)

/-- On an exact power-of-two slice, `k_pow2` returns the slice exponent. -/
@[simp]
theorem k_pow2_pow (t : Nat) : k_pow2 (2 ^ t) = t := by
  unfold k_pow2
  rw [Nat.log_pow (by decide : 1 < 2)]
  rw [if_pos rfl]

/-- The selected power-of-two slice width never exceeds the ambient length. -/
theorem k_pow2_le (n : Nat) : k_pow2 n ≤ n := by
  unfold k_pow2
  by_cases h : n = 2 ^ Nat.log 2 n
  · rw [if_pos h]
    simpa [← h] using le_two_pow_self (Nat.log 2 n)
  · rw [if_neg h]
    exact Nat.zero_le n

/-- The sparse power-of-two selector is unbounded along lengths `2^(B+1)`. -/
theorem k_pow2_unbounded (B : Nat) : ∃ n : Nat, B < k_pow2 n := by
  refine ⟨2 ^ (B + 1), ?_⟩
  rw [k_pow2_pow]
  exact Nat.lt_succ_self B

/-- There are arbitrarily late lengths where the selected width is below `n`. -/
theorem k_pow2_lt_self (N : Nat) : ∃ n : Nat, N ≤ n ∧ k_pow2 n < n := by
  refine ⟨2 ^ (N + 1), ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_succ N) (le_two_pow_self (N + 1))
  · rw [k_pow2_pow]
    exact lt_two_pow_self (N + 1)

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
