-- Partial port of collentropy.lean

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Pnp.BoolFunc

open Classical
open Real

namespace BoolFunc

noncomputable section

variable {n : Nat} [Fintype (Point n)]

/-- Collision probability of a Boolean function `f` under the uniform
measure on `Point n`.  If `p = prob f` is the probability that `f`
outputs `true`, then `collProbFun f = p ^ 2 + (1 - p) ^ 2`. -/
@[simp] def collProbFun (f : BFunc n) : Real :=
  let p := prob f
  p * p + (1 - p) * (1 - p)

/-- Collision entropy of a Boolean function in bits. -/
@[simp] def H₂Fun (f : BFunc n) : Real :=
  -Real.logb 2 (collProbFun f)

lemma collProbFun_const_false : collProbFun (fun _ => false : BFunc n) = 1 := by
  classical
  unfold collProbFun prob ones
  simp

lemma collProbFun_const_true : collProbFun (fun _ => true : BFunc n) = 1 := by
  classical
  unfold collProbFun prob ones
  simp

lemma H₂Fun_const_false :
    H₂Fun (fun _ => false : BFunc n) = 0 := by
  classical
  unfold H₂Fun collProbFun prob ones
  simp

lemma H₂Fun_const_true :
    H₂Fun (fun _ => true : BFunc n) = 0 := by
  classical
  unfold H₂Fun collProbFun prob ones
  simp

lemma collProbFun_ge_half (f : BFunc n) :
    (1 / 2 : ℝ) ≤ collProbFun f := by
  classical
  have h : collProbFun f = (1 / 2 : ℝ) + 2 * (prob f - 1 / 2) ^ 2 := by
    unfold collProbFun
    ring
  have hx : 0 ≤ 2 * (prob f - 1 / 2) ^ 2 := by positivity
  have hx' : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) + 2 * (prob f - 1 / 2) ^ 2 :=
    le_add_of_nonneg_right hx
  exact le_of_le_of_eq hx' h.symm

lemma collProbFun_le_one (f : BFunc n) :
    collProbFun f ≤ 1 := by
  classical
  have hp0 := prob_nonneg (f := f)
  have hp1 := prob_le_one (f := f)
  have h1 : (prob f) ^ 2 ≤ prob f := by
    have := mul_le_mul_of_nonneg_left hp1 hp0
    simpa [pow_two] using this
  have h2 : (1 - prob f) ^ 2 ≤ 1 - prob f := by
    have hle : (1 - prob f) ≤ (1 : ℝ) := by
      have := sub_le_self (a := (1 : ℝ)) (b := prob f) hp0
      simpa using this
    have hpos : 0 ≤ 1 - prob f := by
      have := sub_le_sub_right hp1 (prob f)
      simpa using this
    have := mul_le_mul_of_nonneg_left hle hpos
    simpa [pow_two] using this
  have := add_le_add h1 h2
  simpa [collProbFun, pow_two, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using this.trans_eq (by ring)

lemma collProbFun_pos (f : BFunc n) :
    0 < collProbFun f := by
  have h := collProbFun_ge_half (f := f)
  have : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  exact lt_of_lt_of_le this h

end

end BoolFunc

