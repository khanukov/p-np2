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
and `coverFamily`.  All non‑trivial proofs are left as `sorry` (milestone
**F**), but the *statements* are final and can be used by subsequent
documentation or tests.
-/

import Pnp2.cover
import Pnp2.family_entropy_cover
import Mathlib.Data.Real.Log
import Mathlib.Tactic

open Classical
open Cover
open Boolcube

namespace Bound

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
  -- The inequality clearly holds for small `h` by direct computation.
  -- For larger `h` the right–hand side grows extremely fast since it
  -- contains `2^(10*h)`.
  induction' h with d hd
  · norm_num
  · have hd' : (18 + 22 * d : ℝ) < 100 * (d + 2) * 2 ^ (10 * d) := hd
    -- The step from `d` to `d+1` multiplies the RHS by a factor of
    -- `1024 * (d + 3) / (d + 2)` which easily dominates the additive
    -- increase on the LHS.
    have hrewrite : (18 + 22 * (d + 1) : ℝ)
        = (18 + 22 * d) + 22 := by ring
    have hmul :
        100 * (d + 3) * 2 ^ (10 * (d + 1))
          = 1024 * (100 * (d + 2) * 2 ^ (10 * d)) := by
      ring_nf [pow_succ]
    have hdom :
        (18 + 22 * d : ℝ) + 22
          < 1024 * (100 * (d + 2) * 2 ^ (10 * d)) := by
      have := hd'
      have h22 : (22 : ℝ) < 1024 := by norm_num
      have hpos : (0 : ℝ) ≤ 100 * (d + 2) * 2 ^ (10 * d) := by positivity
      have := add_lt_add_of_lt_of_le this (mul_nonneg (by norm_num) hpos)
      -- squeeze numeric constants; `linarith` closes the goal
      linarith
    simpa [hrewrite, hmul] using hdom

/-- Main numeric inequality: the explicit bound *is* sub‑exponential. -/
lemma mBound_lt_subexp
    (h : ℕ) (n : ℕ) (hn : n ≥ n₀ h) :
    mBound n h < Nat.pow 2 (n / 100) := by
  /-  **Intended proof idea**

      •  Expand `mBound n h = n·(h+2)·2^(10 h)`.
      •  Compare with `2^{n/100}` via logs:
           `log₂(n·…) ≤ log₂ n + …`.
      •  For `n ≥ 10000·…` the RHS < `n/100`. -/
  /-!
  ### Proof Sketch

  Taking base-2 logarithms gives
  `logb 2 (mBound n h)` = `logb 2 n + logb 2 (h + 2) + 10 * h`.
  The assumption `hn : n ≥ n₀ h` rewrites to
  `n ≥ 10000 * (h + 2) * 2 ^ (10 * h)`.  From monotonicity of `logb` we
  deduce

  `logb 2 n ≥ logb 2 (10000) + logb 2 (h + 2) + 10 * h`.

  Rearranging shows

  `logb 2 (mBound n h)` ≤ `logb 2 n + logb 2 (h + 2) + 10 * h` < `n / 100`,

  which implies the desired inequality

  `mBound n h < 2 ^ (n / 100)`
  by the monotonicity of `Real.logb` and exponentiation.
  Formalizing the numeric constants is routine but tedious, so it is
  deferred to future work. -/
  -- A full formal argument requires some tedious growth estimates.
  -- We sketch most of the argument, delegating the last numeric step
  -- to `aux_growth` proved above.
  have n_pos : 0 < n := by
    have hpos : 0 < n₀ h := by
      have : 0 < Nat.pow 2 (10 * h) := pow_pos (by decide) _
      have : 0 < 10000 * (h + 2) * Nat.pow 2 (10 * h) :=
        mul_pos (mul_pos (by decide) (Nat.succ_pos _)) this
      simpa [n₀] using this
    exact lt_of_lt_of_le hpos hn
  -- Casting everything to `ℝ` allows us to compare logarithms.
  have : (mBound n h : ℝ) < (Nat.pow 2 (n / 100) : ℝ) := by
    have npos : 0 < (n : ℝ) := by exact_mod_cast n_pos
    have hpos : 0 < (h + 2 : ℝ) := by positivity
    have hb : (1 : ℝ) < 2 := by norm_num
    -- Expand the logarithm of `mBound`.
    have hlog : Real.logb 2 (mBound n h : ℝ) =
        Real.logb 2 (n : ℝ) + Real.logb 2 (h + 2 : ℝ) + 10 * h := by
      simp [Cover.mBound, Real.logb_mul, npos.ne', hpos.ne',
        Real.logb_pow hb]
    -- Use the bound on `n` given by `hn`.
    have hbase : Real.logb 2 (n : ℝ) ≥
        Real.logb 2 (10000 * (h + 2) * (2 : ℝ) ^ (10 * h)) := by
      have := (Real.logb_le_logb_of_le hb npos)
      have hn' : (10000 * (h + 2) * Nat.pow 2 (10 * h) : ℝ) ≤ n := by
        exact_mod_cast hn
      simpa [pow_mul, Real.rpow_nat_cast] using this hn'
    -- Elementary estimate comparing linear and exponential terms.
    have hgrow : (18 + 22 * h : ℝ) < (n : ℝ) / 100 := by
      have hn' : (100 * (h + 2) * 2 ^ (10 * h) : ℝ) ≤ (n : ℝ) / 100 := by
        have : (100 * (h + 2) * 2 ^ (10 * h) * 100 : ℝ) ≤ n := by
          simpa [n₀, mul_comm, mul_left_comm, mul_assoc] using hn
        exact (le_div_iff_mul_le (by norm_num : (0 : ℝ) < 100)).mpr this
      have haux := aux_growth h
      linarith
    -- Putting everything together and using monotonicity of `Real.logb`.
    have : Real.logb 2 (mBound n h : ℝ) < (n : ℝ) / 100 := by
      have := add_lt_add_right hgrow (Real.logb 2 (n : ℝ))
      have := add_lt_add this (by linarith)
      -- final numeric simplification
      admit
    exact (Real.logb_lt_iff_lt_rpow hb).1 this
  exact_mod_cast this

/-! ## Final packaging: the full FCE‑lemma statement -/

open BoolFunc

variable {n h : ℕ} (F : Family n)

/--
**Family Collision‑Entropy Lemma (β‑version).**

Under the entropy assumption `H₂(F) ≤ h`,
the `coverFamily` constructed in `cover.lean`:

1.  is jointly **monochromatic** on each rectangle;
2.  **covers** every `1`‑input of every `f ∈ F`;
3.  satisfies the **sub‑exponential** bound  
    `|coverFamily| < 2^{n/100}` once `n ≥ n₀(h)`.
-/
theorem FCE_lemma
    (hH : H₂ F ≤ (h : ℝ))
    (hn : n ≥ n₀ h) :
    (coverFamily (n := n) (h := h) F hH).card <
      Nat.pow 2 (n / 100) := by
  -- Combines `coverFamily_card_bound` from `cover.lean`
  -- with the arithmetic lemma above.
  have h1 :=
    Cover.coverFamily_card_bound (n := n) (h := h) F hH
  have h2 :=
    mBound_lt_subexp (h := h) (n := n) hn
  exact lt_of_le_of_lt h1 h2

/--
**Family Collision‑Entropy Lemma.**

Assuming `H₂(F) ≤ h` and `n ≥ n₀(h)`, there exists a finite set of
subcubes that is jointly monochromatic for the entire family and covers
all `1`‑inputs of every `f ∈ F`.  The construction is the
`familyEntropyCover` from `family_entropy_cover.lean`, and the numeric
bound below shows that the cover has at most `2^{n/100}` rectangles. -/
theorem family_collision_entropy_lemma
    (hH : H₂ F ≤ (h : ℝ))
    (hn : n ≥ n₀ h) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (n / 100) := by
  classical
  let FC := Boolcube.familyEntropyCover (F := F) (h := h) hH
  have hlt : FC.rects.card < Nat.pow 2 (n / 100) :=
    lt_of_le_of_lt FC.bound (mBound_lt_subexp (h := h) (n := n) hn)
  have hle : FC.rects.card ≤ Nat.pow 2 (n / 100) := Nat.le_of_lt hlt
  refine ⟨FC.rects, FC.mono, FC.covers, hle⟩

end Bound
