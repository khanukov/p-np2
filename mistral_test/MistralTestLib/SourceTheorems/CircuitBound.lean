/-
  mistral_test/SourceTheorems/CircuitBound.lean
  
  Circuit count bounds for minimal parameters.
  
  For s = 1: circuitCountBound n 1 = n + 2
  For n ≥ 8: n + 2 < 2^(2^n / 2) because 2^n > n + 2 and 2^n ≤ 2^(2^n / 2)
-/
import Models.Model_PartialMCSP

namespace MistralTestLib.CircuitBound

open Pnp3

theorem tableLen_pos_of_n_pos (n : Nat) (_hn : n > 0) : Models.Partial.tableLen n > 0 := by
  simp [Models.Partial.tableLen]

/-- Standard exponential lower bound used by the minimal counting estimate. -/
theorem n_le_two_pow_pred (n : Nat) (hn : 1 ≤ n) : n ≤ 2 ^ (n - 1) := by
  have hlt : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self (n := n - 1)
  omega

/-- For positive exponents, halving `2^n` recovers the predecessor power. -/
theorem half_pow_two_eq_pow_pred (n : Nat) (hn : 1 ≤ n) : 2 ^ n / 2 = 2 ^ (n - 1) := by
  have hs : n = Nat.succ (n - 1) := by omega
  rw [hs, Nat.pow_succ, Nat.mul_comm]
  simp

/-- Basic inequality: `n + 2 < 2^n` once `n ≥ 4`. -/
theorem n_plus_two_lt_pow_two_n (n : Nat) (hn : n ≥ 4) : n + 2 < 2 ^ n := by
  have hmain : n ≤ 2 ^ (n - 1) := n_le_two_pow_pred n (by omega)
  have hlt : n + 2 < 2 * n := by omega
  calc
    n + 2 < 2 * n := hlt
    _ ≤ 2 * 2 ^ (n - 1) := by gcongr
    _ = 2 ^ n := by
      have hs : n = Nat.succ (n - 1) := by omega
      rw [hs, Nat.pow_succ]
      simp [Nat.mul_comm]

/-- Basic inequality: `n ≤ 2^n / 2` once `n ≥ 4`. -/
theorem n_le_half_pow_two_n (n : Nat) (hn : n ≥ 4) : n ≤ 2 ^ n / 2 := by
  rw [half_pow_two_eq_pow_pred n (by omega)]
  exact n_le_two_pow_pred n (by omega)

/-!
Final theorem: `circuitCountBound n 1 < 2^(2^n/2)` for `n ≥ 8`.

Proof:
  `circuitCountBound n 1 = n + 2`
  `n + 2 < 2^n` (by `n_plus_two_lt_pow_two_n`)
  `2^n ≤ 2^(2^n / 2)` because `n ≤ 2^n / 2` (by `n_le_half_pow_two_n`)
-/
theorem circuit_bound_ok_minimal (n : Nat) (hn : n ≥ 8) :
    Models.circuitCountBound n 1 < 2 ^ (Models.Partial.tableLen n / 2) := by
  have h1 : Models.circuitCountBound n 1 = n + 2 := by
    simp [Models.circuitCountBound]
  rw [h1]
  have h2 : Models.Partial.tableLen n = 2 ^ n := by
    simp [Models.Partial.tableLen]
  rw [h2]
  have h3 : n + 2 < 2^n := n_plus_two_lt_pow_two_n n (by omega)
  have h4 : 2^n ≤ 2^(2^n / 2) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    exact n_le_half_pow_two_n n (by omega)
  calc
    n + 2 < 2^n := h3
    _ ≤ 2^(2^n / 2) := h4

end MistralTestLib.CircuitBound
