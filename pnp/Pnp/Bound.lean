/-
bound.lean
===========

Pure *arithmetic* lemmas that translate the explicit counting bound  
`|𝓡| ≤ n·(h+2)·2^(10 h)` (proved in `cover.lean`) into the convenient
*sub‑exponential* tail bound that appears in every prose version of the
Family Collision‑Entropy Lemma:

> for sufficiently large `n` we have  
> `n·(h+2)·2^(10 h) < 2^{n / 100}`.

The file is intentionally **isolated** from the combinatorial logic:
its only imports are earlier modules for the *definitions* of `mBound`
and `coverFamily`.  The numeric arguments are nontrivial and currently
sketched at the end of this file, but the statements are final and can be
used by subsequent documentation or tests.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical

namespace Bound

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

/-! ## Elementary growth estimates -/

/-- A *convenience constant* `n₀(h)` such that  
    for all `n ≥ n₀(h)` we have  
    `n·(h+2)·2^(10 h) < 2^{n/100}`.  

    The closed‑form we pick (far from optimal) is  
    `n₀(h) = 10 000 · (h + 2) · 2^(10 h)`.  -/
def n₀ (h : ℕ) : ℕ :=
  10000 * (h + 2) * Nat.pow 2 (10 * h)

/-!  A crude growth estimate used in the proof of `mBound_lt_subexp`.
    It simply bounds a linear expression in `h` by the dominating
    exponential term appearing in `n₀`.  The statement is far from sharp
    but suffices for our purposes.  -/
lemma aux_growth (h : ℕ) :
    (18 + 22 * h : ℝ) < 100 * (h + 2) * 2 ^ (10 * h) := by
  -- The inequality is trivial for small `h` and grows stronger
  -- for larger values because the right-hand side contains the
  -- rapidly growing factor `2^(10*h)`.
  induction' h with d hd
  · norm_num
  · have hd' : (18 + 22 * d : ℝ) < 100 * (d + 2) * 2 ^ (10 * d) := hd
    -- Compare the step from `d` to `d + 1`.
    have hrewrite : (18 + 22 * (d + 1) : ℝ) = (18 + 22 * d) + 22 := by ring
    have hmul :
        100 * (d + 3) * 2 ^ (10 * (d + 1)) =
          1024 * (100 * (d + 2) * 2 ^ (10 * d)) := by
      ring_nf [pow_succ]
    have hdom :
        (18 + 22 * d : ℝ) + 22 <
          1024 * (100 * (d + 2) * 2 ^ (10 * d)) := by
      have hpos : (0 : ℝ) ≤ 100 * (d + 2) * 2 ^ (10 * d) := by positivity
      have h22 : (22 : ℝ) < 1024 := by norm_num
      have := add_lt_add_of_lt_of_le hd' (mul_nonneg (by norm_num) hpos)
      linarith
    simpa [hrewrite, hmul] using hdom

lemma mBound_lt_subexp
    (h : ℕ) (n : ℕ) (hn : n ≥ n₀ h) :
    mBound n h < Nat.pow 2 (n / 100) := by
  -- A sketch of the usual logarithmic comparison.
  have n_pos : 0 < n := by
    have hpos : 0 < n₀ h := by
      have : 0 < Nat.pow 2 (10 * h) := pow_pos (by decide) _
      have : 0 < 10000 * (h + 2) * Nat.pow 2 (10 * h) :=
        mul_pos (mul_pos (by decide) (Nat.succ_pos _)) this
      simpa [n₀] using this
    exact lt_of_lt_of_le hpos hn
  have : (mBound n h : ℝ) < (Nat.pow 2 (n / 100) : ℝ) := by
    have npos : 0 < (n : ℝ) := by exact_mod_cast n_pos
    have hpos : 0 < (h + 2 : ℝ) := by positivity
    have hb : (1 : ℝ) < 2 := by norm_num
    -- Expand the logarithm of `mBound`.
    have hlog : Real.logb 2 (mBound n h : ℝ) =
        Real.logb 2 (n : ℝ) + Real.logb 2 (h + 2 : ℝ) + 10 * h := by
      simp [mBound, Real.logb_mul, npos.ne', hpos.ne', Real.logb_pow hb]
    -- Control the `logb` of `n` using the assumption `hn`.
    have hbase : Real.logb 2 (n : ℝ) ≥
        Real.logb 2 (10000 * (h + 2) * (2 : ℝ) ^ (10 * h)) := by
      have := (Real.logb_le_logb_of_le hb npos)
      have hn' : (10000 * (h + 2) * Nat.pow 2 (10 * h) : ℝ) ≤ n := by
        exact_mod_cast hn
      simpa [pow_mul, Real.rpow_nat_cast] using this hn'
    -- Relate linear and exponential growth.
    have hgrow : (18 + 22 * h : ℝ) < (n : ℝ) / 100 := by
      have hn' : (100 * (h + 2) * 2 ^ (10 * h) : ℝ) ≤ (n : ℝ) / 100 := by
        have : (100 * (h + 2) * 2 ^ (10 * h) * 100 : ℝ) ≤ n := by
          simpa [n₀, mul_comm, mul_left_comm, mul_assoc] using hn
        exact (le_div_iff_mul_le (by norm_num : (0 : ℝ) < 100)).mpr this
      have haux := aux_growth h
      linarith
    -- Conclude using monotonicity of the logarithm.
    have : Real.logb 2 (mBound n h : ℝ) < (n : ℝ) / 100 := by
      have := add_lt_add_right hgrow (Real.logb 2 (n : ℝ))
      have := add_lt_add this (by linarith)
      have := add_lt_add_right this (Real.logb 2 (h + 2 : ℝ))
      have := add_lt_add_right this (10 * h)
      simpa [hlog] using this
    exact (Real.logb_lt_iff_lt_rpow hb).1 this
  exact_mod_cast this

end Bound
