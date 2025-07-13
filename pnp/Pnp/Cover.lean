import Pnp.BoolFunc
import Pnp.Agreement
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Classical
open BoolFunc
open Finset
open Agreement

namespace Cover

/-! ## Numeric bound -/

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

lemma numeric_bound (n h : ℕ) (hn : 0 < n) : 2 * h + n ≤ mBound n h := by
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.one_le_pow _ _ (by decide : 0 < (2 : ℕ))
  have hlin : (2 * h + n : ℤ) ≤ (n : ℤ) * (h + 2) := by
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have h0 : 0 ≤ (h : ℤ) := by exact_mod_cast Nat.zero_le _
    nlinarith
  have hlin_nat : (2 * h + n : ℕ) ≤ n * (h + 2) := by exact_mod_cast hlin
  have hstep : n * (h + 2) ≤ n * (h + 2) * 2 ^ (10 * h) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Nat.mul_le_mul_left (n * (h + 2)) hpow
  have hmul : (2 * h + n : ℕ) ≤ n * (h + 2) * 2 ^ (10 * h) :=
    le_trans hlin_nat hstep
  simpa [mBound] using hmul

end Cover
