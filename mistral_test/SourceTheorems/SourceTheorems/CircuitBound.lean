/-
  mistral_test/SourceTheorems/CircuitBound.lean
  
  Circuit count bounds for minimal parameters.
  
  For s = 1: circuitCountBound n 1 = n + 2
  For n ≥ 8: n + 2 < 2^(2^n / 2) because 2^n > n + 2 and 2^n ≤ 2^(2^n / 2)
-/
import Pnp3.Core

namespace MistralTestLib

open Pnp3 Core

theorem tableLen_pos_of_n_pos (n : Nat) (hn : n > 0) : Partial.tableLen n > 0 := by
  simp[Partial.tableLen]; omega

/-! Basic inequality: n + 2 < 2^n for n ≥ 4 -/
theorem n_plus_two_lt_pow_two_n (n : Nat) (hn : n ≥ 4) : n + 2 < 2 ^ n := by
  -- Base case: n = 4
  have base4 : 4 + 2 < 2^4 := by norm_num
  -- Inductive step
  have step : ∀ k ≥ 4, k + 2 < 2^k → (k+1) + 2 < 2^(k+1) := by
    intro k hk h_ih
    calc (k+1) + 2 = k + 3 := by ring
      _ < 2^k + 1 := by omega
      _ ≤ 2^k + 2^k := by omega
      _ = 2^(k+1) := by ring
  -- Full induction
  have mono : ∀ m ≥ 4, m + 2 < 2^m := by
    intro m hm
    induction m, hm with
    | base => exact base4
    | ih k hk ih => exact step k hk ih
  exact mono n hn

/-! Basic inequality: n ≤ 2^n / 2 for n ≥ 4 -/
theorem n_le_half_pow_two_n (n : Nat) (hn : n ≥ 4) : n ≤ 2^n / 2 := by
  -- Base case: n = 4
  have base4 : 4 ≤ 2^4 / 2 := by norm_num
  -- Inductive step
  have step : ∀ k ≥ 4, k ≤ 2^k / 2 → k+1 ≤ 2^(k+1) / 2 := by
    intro k hk h_ih
    calc k+1 ≤ 2^k / 2 + 1 := by omega
      _ ≤ 2^k / 2 + 2^k / 2 := by
        have : 1 ≤ 2^k / 2 := by
          have : 4 ≤ k := by omega
          have : 8 ≤ 2^k := by
            have : 2^4 = 16 := by norm_num
            have : 2^k ≥ 2^4 := Nat.pow_le_pow_right (by norm_num) hk
            omega
          omega
        omega
      _ = 2^k := by omega
      _ = 2^(k+1) / 2 := by ring
  -- Full induction
  have mono : ∀ m ≥ 4, m ≤ 2^m / 2 := by
    intro m hm
    induction m, hm with
    | base => exact base4
    | ih k hk ih => exact step k hk ih
  exact mono n hn

/-! 
Final theorem: circuitCountBound n 1 < 2^(2^n/2) for n ≥ 8.

Proof:
  circuitCountBound n 1 = n + 2
  n + 2 < 2^n (by n_plus_two_lt_pow_two_n)
  2^n ≤ 2^(2^n / 2) because n ≤ 2^n / 2 (by n_le_half_pow_two_n) and 1 < 2
-/
theorem circuit_bound_ok_minimal (n : Nat) (hn : n ≥ 8) :
    circuitCountBound n 1 < 2 ^ (Partial.tableLen n / 2) := by
  -- Step 1: circuitCountBound n 1 = n + 2
  have h1 : circuitCountBound n 1 = n + 2 := by
    simp [circuitCountBound]
    all_goals omega
  rw [h1]
  
  -- Step 2: Partial.tableLen n = 2^n
  have h2 : Partial.tableLen n = 2^n := by simp [Partial.tableLen]
  rw [h2]
  
  -- Step 3: n + 2 < 2^n
  have h3 : n + 2 < 2^n := n_plus_two_lt_pow_two_n n (by omega)
  
  -- Step 4: n ≤ 2^n / 2, so 2^n ≤ 2^(2^n / 2)
  have h4 : 2^n ≤ 2^(2^n / 2) := by
    apply Nat.pow_le_pow_right (by norm_num : 1 < 2)
    exact n_le_half_pow_two_n n (by omega)
  
  -- Conclusion
  calc n + 2 < 2^n := h3
    _ ≤ 2^(2^n / 2) := h4

end MistralTestLib
