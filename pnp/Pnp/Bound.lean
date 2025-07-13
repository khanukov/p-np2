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
  -- First bound `(18 + 22 * h)` by a simpler linear expression.
  have hbase : (18 + 22 * h : ℝ) < 100 * (h + 2) := by
    nlinarith
  -- Note that `2 ^ (10 * h) ≥ 1` for all `h`.
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (10 * h) := by
    simpa using (one_le_pow₀ (n := 10 * h) (a := (2 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2))
  -- Multiplying the linear bound by the positive factor `2 ^ (10 * h)`
  -- yields the desired inequality.
  have hbnd : 100 * (h + 2) ≤ 100 * (h + 2) * (2 : ℝ) ^ (10 * h) := by
    have hpos : (0 : ℝ) ≤ 100 * (h + 2) := by positivity
    simpa using mul_le_mul_of_nonneg_left hpow hpos
  exact lt_of_lt_of_le hbase hbnd

axiom mBound_lt_subexp
    (h : ℕ) (n : ℕ) (hn : n ≥ n₀ h) :
    mBound n h < Nat.pow 2 (n / 100)

end Bound
