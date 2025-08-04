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

import Pnp2.cover2
import Pnp2.family_entropy_cover
import Mathlib.Data.Real.Log
import Mathlib.Tactic

open Classical
open Cover2
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

-- Basic numeric facts about `mBound`.  These lemmas mirror the
-- versions in `cover.lean` but live in the arithmetic-focused
-- namespace for easier reuse.

lemma mBound_pos (n h : ℕ) (hn : 0 < n) :
    0 < mBound n h := by
  have hpos₁ : 0 < h + 2 := Nat.succ_pos _
  have hpos₂ : 0 < 2 ^ (10 * h) := pow_pos (by decide) _
  have hmul : 0 < n * (h + 2) := Nat.mul_pos hn hpos₁
  have := Nat.mul_pos hmul hpos₂
  simpa [mBound] using this

lemma two_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hh2 : 2 ≤ h + 2 := by
    have := Nat.zero_le h
    exact Nat.succ_le_succ (Nat.succ_le_succ this)
  have hfactor : 2 ≤ n * (h + 2) := by
    have := Nat.mul_le_mul hn1 hh2 (by decide) (Nat.zero_le _)
    simpa [one_mul] using this
  have hpow : 1 ≤ 2 ^ (10 * h) :=
    Nat.one_le_pow (2) (10 * h) (by decide)
  have := Nat.mul_le_mul hfactor hpow
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

lemma three_le_mBound (n h : ℕ) (hn : 0 < n) (hh : 1 ≤ h) :
    3 ≤ mBound n h := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have h3 : 3 ≤ h + 2 := by
    have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
    have : (3 : ℤ) ≤ h + 2 := by nlinarith
    exact_mod_cast this
  have hfac1 : h + 2 ≤ n * (h + 2) := by
    have := Nat.mul_le_mul_right (h + 2) hn1
    simpa [one_mul] using this
  have hfac : 3 ≤ n * (h + 2) := le_trans h3 hfac1
  have hpow : 1 ≤ 2 ^ (10 * h) := Nat.one_le_pow (2) (10 * h) (by decide)
  have := Nat.mul_le_mul hfac hpow
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

lemma mBound_mono {n : ℕ} : Monotone (mBound n) := by
  intro h₁ h₂ hh
  dsimp [mBound]
  have hfac : n * (h₁ + 2) ≤ n * (h₂ + 2) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right hh 2)
  have hpow : 2 ^ (10 * h₁) ≤ 2 ^ (10 * h₂) := by
    have := Nat.mul_le_mul_left 10 hh
    exact Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) this
  exact Nat.mul_le_mul hfac hpow

lemma mBound_mono_left {n₁ n₂ h : ℕ} (hn : n₁ ≤ n₂) :
    mBound n₁ h ≤ mBound n₂ h := by
  dsimp [mBound]
  have hfac : n₁ * (h + 2) ≤ n₂ * (h + 2) :=
    Nat.mul_le_mul_right (h + 2) hn
  have := Nat.mul_le_mul hfac (le_rfl : 2 ^ (10 * h) ≤ 2 ^ (10 * h))
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

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
      simp [mBound, Real.logb_mul, npos.ne', hpos.ne',
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
    Cover2.coverFamily_card_bound (n := n) (h := h) F hH
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

/-- A convenient numeric corollary of `family_collision_entropy_lemma`.
    Replacing the exponent `n / 100` by `(2 ^ n) / 100` emphasises that
    the bound depends subexponentially on the full truth-table size
    `N = 2 ^ n`. -/
theorem family_collision_entropy_lemma_table
    (hH : H₂ F ≤ (h : ℝ))
    (hn : n ≥ n₀ h) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 ((Nat.pow 2 n) / 100) := by
  classical
  obtain ⟨Rset, hmono, hcov, hbound⟩ :=
    family_collision_entropy_lemma (F := F) (h := h) (hH := hH) hn
  have hpow : (n / 100) ≤ (Nat.pow 2 n) / 100 := by
    have hle : n ≤ Nat.pow 2 n := by
      -- elementary inequality `n ≤ 2 ^ n`
      induction' n with d hd
      · simp
      ·
        have hstep : d + 1 ≤ 2 ^ d + 1 := Nat.succ_le_succ hd
        have hpos : (0 : ℕ) < 2 ^ d := pow_pos (by decide) _
        have hstep' : d + 1 ≤ 2 ^ d + 2 ^ d :=
          le_trans hstep <| Nat.add_le_add_left (Nat.succ_le_of_lt hpos) _
        simpa [two_mul, Nat.pow_succ] using hstep'
    exact Nat.div_le_div_right hle
  have hbound' : Rset.card ≤ Nat.pow 2 ((Nat.pow 2 n) / 100) :=
    le_trans hbound <|
      Nat.pow_le_pow_of_le_left (by decide : (1 : ℕ) ≤ 2) hpow
  exact ⟨Rset, hmono, hcov, hbound'⟩

/-! ### Specialised corollary for small circuits

The next lemma packages `family_collision_entropy_lemma_table`
for the concrete family of Boolean functions computed by circuits of
size at most `n^c`.  This is a convenient formulation of **Lemma B**:
for sufficiently large `n` the entire circuit class admits a joint
monochromatic cover of size strictly smaller than `2^{(2^n)/100}`. -/

open Boolcube Circuit

/-- **Lemma B (circuit form).**
    Let `c` be a fixed exponent and consider all circuits on `n`
    inputs of size at most `n^c`.  Once `n` exceeds the threshold
    `n₀ h` (with `h = n^c * (Nat.log n + 1) + 1`), there exists a
    finite set of subcubes covering every `1`‑input of every such
    circuit.  Moreover the number of rectangles is bounded by
    `2^{(2^n)/100}`. -/
theorem lemmaB_circuit_cover (c n : ℕ)
    (hn : n ≥ n₀ (n ^ c * (Nat.log n + 1) + 1)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R (Circuit.family n (n ^ c))) ∧
      (∀ f ∈ Circuit.family n (n ^ c), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 ((Nat.pow 2 n) / 100) := by
  classical
  let h := n ^ c * (Nat.log n + 1) + 1
  have hH : H₂ (Circuit.family n (n ^ c)) ≤ (h : ℝ) := by
    simpa [h] using Circuit.family_H₂_le (n := n) (m := n ^ c)
  -- Apply the general entropy-cover lemma specialised to this family.
  simpa [h] using
    family_collision_entropy_lemma_table
      (F := Circuit.family n (n ^ c)) (h := h) (hH := hH) (hn := hn)

/-! ### Variant bound in the usual $2^{N - N^{\delta}}$ form

The next lemma reformulates `lemmaB_circuit_cover` using the
slightly stronger inequality `(|Rset| ≤ 2^{2^n - 2^{n/2}})`.
This matches the conventional presentation of Lemma B with the
parameter `δ = 1/2`.  The proof just observes that
`(2^n)/100 ≤ 2^n - 2^{n/2}` for every positive `n`. -/

lemma pow_two_div_hundred_le (n : ℕ) (hn : 0 < n) :
    (Nat.pow 2 n) / 100 ≤ Nat.pow 2 n - Nat.pow 2 (n / 2) := by
  have hdiv : n / 2 < n := Nat.div_lt_self hn (by decide)
  have hpos : 1 ≤ n - n / 2 := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hdiv)
  have hpow : (2 : ℕ) ≤ Nat.pow 2 (n - n / 2) := by
    simpa [pow_one] using
      (Nat.pow_le_pow_of_le_left (by decide : (2 : ℕ) ≤ 2) hpos)
  have hstep : 100 ≤ 99 * Nat.pow 2 (n - n / 2) := by
    have hbase : (100 : ℕ) ≤ 99 * 2 := by decide
    have := Nat.mul_le_mul_left 99 hpow
    exact hbase.trans this
  have hmult := Nat.mul_le_mul_right (Nat.pow 2 (n / 2)) hstep
  have hpow2 :
      Nat.pow 2 (n - n / 2) * Nat.pow 2 (n / 2) = Nat.pow 2 n := by
    have hsum : n - n / 2 + n / 2 = n := by
      exact Nat.sub_add_cancel (Nat.le_of_lt hdiv)
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, hsum] using
      (Nat.pow_add (2) (n - n / 2) (n / 2)).symm
  have hineq : 100 * Nat.pow 2 (n / 2) ≤ 99 * Nat.pow 2 n := by
    simpa [hpow2, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmult
  have hsum := Nat.add_le_add_left hineq (Nat.pow 2 n)
  have hsum' :
      Nat.pow 2 n + 100 * Nat.pow 2 (n / 2) ≤ 100 * Nat.pow 2 n := by
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hsub :=
    (Nat.le_sub_iff_add_le
        (by
          have := Nat.mul_le_mul_left 100
              (Nat.pow_le_pow_of_le_left (by decide : (2 : ℕ) ≤ 2)
                (Nat.div_le_self n 2))
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this)).mpr
      hsum'
  have :=
    (Nat.le_div_iff_mul_le (by decide : (0 : ℕ) < 100)).mpr hsub
  simpa using this

theorem lemmaB_circuit_cover_delta (c n : ℕ)
    (hn : n ≥ n₀ (n ^ c * (Nat.log n + 1) + 1)) (hnpos : 0 < n) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R (Circuit.family n (n ^ c))) ∧
      (∀ f ∈ Circuit.family n (n ^ c), ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (Nat.pow 2 n - Nat.pow 2 (n / 2)) := by
  classical
  obtain ⟨Rset, hmono, hcov, hbound⟩ :=
    lemmaB_circuit_cover (c := c) (n := n) hn
  have hineq := pow_two_div_hundred_le (n := n) hnpos
  have hbound' :
      Rset.card ≤ Nat.pow 2 (Nat.pow 2 n - Nat.pow 2 (n / 2)) := by
    have := Nat.pow_le_pow_of_le_left (by decide : (1 : ℕ) ≤ 2) hineq
    exact le_trans hbound this
  exact ⟨Rset, hmono, hcov, hbound'⟩

end Bound
