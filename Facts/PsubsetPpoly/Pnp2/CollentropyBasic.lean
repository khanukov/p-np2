import Pnp2.BoolFunc
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Classical
open Real

namespace BoolFunc

variable {n : ℕ} [Fintype (Point n)]

/-! ## Collision entropy
A minimized version providing only what is needed for the SAT solver.
-/

/-- Collision probability of `f` under the uniform distribution. -/
@[simp] noncomputable def collProbFun (f : BFunc n) : ℝ :=
  let p := prob f
  p * p + (1 - p) * (1 - p)

/-- Collision entropy of a Boolean function in bits. -/
@[simp] noncomputable def H₂Fun (f : BFunc n) : ℝ :=
  -Real.logb 2 (collProbFun f)

lemma collProbFun_eq_one_sub (f : BFunc n) :
    collProbFun f = 1 - 2 * prob f * (1 - prob f) := by
  classical
  have : prob f * prob f + (1 - prob f) * (1 - prob f)
      = 1 - 2 * prob f * (1 - prob f) := by ring
  simpa [collProbFun] using this

lemma prob_mul_le_quarter (f : BFunc n) :
    prob f * (1 - prob f) ≤ (1 / 4 : ℝ) := by
  classical
  -- Rewrite the product in a completed-square form.
  have hsq : prob f * (1 - prob f)
      = (1 / 4 : ℝ) - (prob f - 1 / 2) ^ 2 := by ring
  -- Squares are nonnegative, hence the product is at most `1/4`.
  have hnonneg : 0 ≤ (prob f - 1 / 2) ^ 2 := by positivity
  have := sub_le_self (a := (1 / 4 : ℝ)) (b := (prob f - 1 / 2) ^ 2) hnonneg
  simpa [hsq] using this

lemma collProbFun_ge_half (f : BFunc n) :
    (1 / 2 : ℝ) ≤ collProbFun f := by
  classical
  -- Using `prob_mul_le_quarter`, rewrite the bound in terms of the product
  -- `prob f * (1 - prob f)`.
  have hprod := prob_mul_le_quarter (f := f)
  have hprod' : 2 * (prob f * (1 - prob f)) ≤ (1 / 2 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hprod (by norm_num : 0 ≤ (2 : ℝ))
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have := sub_le_sub_left hprod' (1 : ℝ)
  -- `collProbFun` expands to `1 - 2 * prob f * (1 - prob f)`.
  simpa [collProbFun_eq_one_sub, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc] using this

lemma collProbFun_le_one (f : BFunc n) :
    collProbFun f ≤ 1 := by
  classical
  -- The term `2 * prob f * (1 - prob f)` is nonnegative.
  have hnonneg : 0 ≤ 2 * prob f * (1 - prob f) := by
    have hprod : 0 ≤ prob f * (1 - prob f) := by
      have hp0 := prob_nonneg (f := f)
      have hp1 := sub_nonneg.mpr (prob_le_one (f := f))
      exact mul_nonneg hp0 hp1
    have : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg this hprod
  -- Hence `1 - 2 * prob f * (1 - prob f) ≤ 1`.
  have := sub_le_self (a := (1 : ℝ)) (b := 2 * prob f * (1 - prob f)) hnonneg
  simpa [collProbFun_eq_one_sub, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc, mul_comm, mul_left_comm, mul_assoc] using this

lemma H₂Fun_le_one (f : BFunc n) :
    H₂Fun f ≤ 1 := by
  classical
  -- Bounds for `collProbFun f`.
  have hge := collProbFun_ge_half (f := f)
  have hle := collProbFun_le_one (f := f)
  have hpos : 0 < collProbFun f := by
    have : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hge
  -- Use monotonicity of `Real.logb` with base `2` (> 1).
  have hb : 1 < (2 : ℝ) := by norm_num
  have hlog_le_zero : Real.logb 2 (collProbFun f) ≤ 0 :=
    (Real.logb_le_logb_of_le hb hpos hle)
  have hlog_ge_neg_one : -1 ≤ Real.logb 2 (collProbFun f) := by
    have := Real.logb_le_logb_of_le hb (by norm_num : 0 < (1 / 2 : ℝ)) hge
    exact this
  -- Translate the bounds on the logarithm to the entropy.
  have h0 : 0 ≤ H₂Fun f := by
    have := neg_nonneg.mpr hlog_le_zero
    simpa [H₂Fun] using this
  have h1 : H₂Fun f ≤ 1 := by
    have := neg_le_neg hlog_ge_neg_one
    have hval : -Real.logb 2 (1 / 2 : ℝ) = (1 : ℝ) := by
      have h := Real.logb_inv (2 : ℝ) 2
      have : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
      simpa [this] using congrArg Neg.neg h
    simpa [H₂Fun, hval] using this
  exact h1

end BoolFunc

