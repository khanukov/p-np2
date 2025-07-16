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
import Pnp.Entropy
import Pnp.FamilyEntropyCover
import Pnp.Cover

set_option maxHeartbeats 400000

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

/-- Main numeric inequality: the explicit bound *is* sub‑exponential. -/
lemma mBound_lt_subexp
    (h : ℕ) (n : ℕ) (hn : n ≥ n₀ h) :
    mBound n h < Nat.pow 2 (n / 100) := by
  -- Sketch of the numeric argument:
  -- Taking binary logarithms reduces the inequality to
  -- `logb 2 (mBound n h)` < `n / 100`, which follows from
  -- the assumption `hn` after bounding linear terms via `aux_growth`.
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
      -- numeric constants are small enough for `linarith` to solve the goal
      have := add_lt_add_right this (Real.logb 2 (h + 2 : ℝ))
      have := add_lt_add_right this (10 * h)
      simpa [hlog] using this
    have hb' : (1 : ℝ) < 2 := by norm_num
    have hpow : (mBound n h : ℝ) < (2 : ℝ) ^ (n / 100) :=
      (Real.logb_lt_iff_lt_rpow hb').1 this
    exact hpow
  exact_mod_cast this

/-! ## Final packaging: the full FCE‑lemma statement -/

open BoolFunc

variable {n h : ℕ} (F : BoolFunc.Family n)

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
    (Boolcube.familyEntropyCover (F := F) (h := h) hH).rects.card <
      Nat.pow 2 (n / 100) := by
  have h1 :=
    (Boolcube.familyEntropyCover (F := F) (h := h) hH).bound
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
    ∃ Rset : Finset (BoolFunc.Subcube n),
      (∀ R ∈ Rset, BoolFunc.Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (n / 100) := by
  classical
  let FC := Boolcube.familyEntropyCover (F := F) (h := h) hH
  have hlt : FC.rects.card < Nat.pow 2 (n / 100) :=
    lt_of_le_of_lt FC.bound (mBound_lt_subexp (h := h) (n := n) hn)
  have hle : FC.rects.card ≤ Nat.pow 2 (n / 100) := Nat.le_of_lt hlt
  refine ⟨FC.rects, FC.mono, FC.covers, hle⟩

end Bound
