/-
collentropy.lean
=================

This module defines the collision entropy of a single Boolean function
`f : Point n → Bool`.  The quantity measures how close the output
probability distribution of `f` is to uniform.

For a Boolean random variable with probability `p` of being `true`, the
collision entropy is `-log₂ (p^2 + (1-p)^2)`.
We provide the basic definition and show that constant functions have
zero collision entropy.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Pnp.BoolFunc

open Classical
open Real

namespace BoolFunc

noncomputable section

variable {n : ℕ} [Fintype (Point n)]

/-- Collision probability of a Boolean function `f` under the uniform
measure on `Point n`.  If `p = prob f` is the probability that `f`
outputs `true`, then `collProbFun f = p^2 + (1 - p)^2`. -/
@[simp] def collProbFun (f : BFunc n) : ℝ :=
  let p := prob f
  p * p + (1 - p) * (1 - p)

/-- Collision entropy of a Boolean function in bits. -/
@[simp] def H₂Fun (f : BFunc n) : ℝ :=
  -Real.logb 2 (collProbFun f)

lemma collProbFun_const_false : collProbFun (fun _ => false : BFunc n) = 1 := by
  simp [collProbFun, prob]

lemma collProbFun_const_true : collProbFun (fun _ => true : BFunc n) = 1 := by
  simp [collProbFun, prob]

lemma H₂Fun_const_false :
    H₂Fun (fun _ => false : BFunc n) = 0 := by
  simp [H₂Fun, collProbFun_const_false]

lemma H₂Fun_const_true :
    H₂Fun (fun _ => true : BFunc n) = 0 := by
  simp [H₂Fun, collProbFun_const_true]

lemma collProbFun_ge_half (f : BFunc n) :
    (1 / 2 : ℝ) ≤ collProbFun f := by
  classical
  have h : collProbFun f = (1 / 2 : ℝ) + 2 * (prob f - 1 / 2) ^ 2 := by
    field_simp [collProbFun, pow_two, sub_eq_add_neg, mul_add, add_mul, mul_comm,
      mul_left_comm, mul_assoc, add_comm, add_left_comm, sub_eq_add_neg]
  have hsq : 0 ≤ (prob f - 1 / 2) ^ 2 := by positivity
  have : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) + 2 * (prob f - 1 / 2) ^ 2 := by
    have hx : 0 ≤ 2 * (prob f - 1 / 2) ^ 2 := by positivity
    exact le_add_of_nonneg_right hx
  simpa [h] using this

lemma collProbFun_le_one (f : BFunc n) :
    collProbFun f ≤ 1 := by
  classical
  have hp0 := prob_nonneg (f := f)
  have hp1 := prob_le_one (f := f)
  have h1 : (prob f) ^ 2 ≤ prob f := by
    have := mul_le_mul_of_nonneg_left hp1 hp0
    simpa [pow_two] using this
  have h2 : (1 - prob f) ^ 2 ≤ 1 - prob f := by
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right hp1 _) (by positivity)
    simpa [pow_two] using this
  have := add_le_add h1 h2
  simpa [collProbFun, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using this.trans_eq (by ring)

lemma collProbFun_pos (f : BFunc n) :
    0 < collProbFun f := by
  have h := collProbFun_ge_half (f := f)
  have : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  exact lt_of_lt_of_le this h

lemma H₂Fun_nonneg (f : BFunc n) :
    0 ≤ H₂Fun f := by
  classical
  have hle := collProbFun_le_one (f := f)
  have hpos := collProbFun_pos (f := f)
  have := Real.logb_nonpos (b := 2) (by norm_num) (by exact_mod_cast hle)
  have := neg_nonneg.mpr this
  simpa [H₂Fun] using this

lemma H₂Fun_le_one (f : BFunc n) :
    H₂Fun f ≤ 1 := by
  classical
  have hge := collProbFun_ge_half (f := f)
  have hpos := collProbFun_pos (f := f)
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hge
  have hneg := neg_le_neg hlog
  have h1 : (-Real.logb 2 (collProbFun f)) ≤ (-Real.logb 2 (1 / 2 : ℝ)) := by
    simpa using hneg
  have := h1
  have h1half : (-Real.logb 2 (1 / 2 : ℝ)) = (1 : ℝ) := by
    simp [Real.logb_inv]
  simpa [H₂Fun, h1half] using this

lemma H₂Fun_prob_half (f : BFunc n) (h : prob f = 1 / 2) :
    H₂Fun f = 1 := by
  classical
  have : collProbFun f = 1 / 2 := by
    simp [collProbFun, h, pow_two]
  simp [H₂Fun, this]

end

end BoolFunc

