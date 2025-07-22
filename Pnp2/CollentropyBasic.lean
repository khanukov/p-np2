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
  have hsq : 0 ≤ (prob f - 1 / 2 : ℝ) ^ 2 := by positivity
  have hrepr : prob f * (1 - prob f) = 1 / 4 - (prob f - 1 / 2) ^ 2 := by ring
  have hx : 1 / 4 - (prob f - 1 / 2) ^ 2 ≤ 1 / 4 := by exact sub_le_self _ hsq
  simpa [hrepr] using hx

lemma collProbFun_ge_half (f : BFunc n) :
    (1 / 2 : ℝ) ≤ collProbFun f := by
  classical
  have h := prob_mul_le_quarter (f := f)
  have hrepr := collProbFun_eq_one_sub (f := f)
  have hx : 2 * prob f * (1 - prob f) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have := sub_le_sub_left hx 1
  simpa [hrepr] using this

lemma collProbFun_le_one (f : BFunc n) :
    collProbFun f ≤ 1 := by
  classical
  have hnonneg : 0 ≤ prob f * (1 - prob f) := by
    have hp0 := prob_nonneg (f := f)
    have hp1 := sub_nonneg.mpr (prob_le_one (f := f))
    exact mul_nonneg hp0 hp1
  have hrepr := collProbFun_eq_one_sub (f := f)
  have hx : 1 - 2 * prob f * (1 - prob f) ≤ 1 := by
    have hx' : -(2 * prob f * (1 - prob f)) ≤ 0 := by
      have hx'' : (0 : ℝ) ≤ 2 * prob f * (1 - prob f) := by positivity
      simpa using neg_nonpos.mpr hx''
    have := add_le_add_left hx' 1
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  simpa [hrepr] using hx

lemma H₂Fun_le_one (f : BFunc n) :
    H₂Fun f ≤ 1 := by
  classical
  have hge := collProbFun_ge_half (f := f)
  have hpos : 0 < collProbFun f :=
    (lt_of_le_of_lt hge (by norm_num : (1 / 2 : ℝ) < 2))
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hge
  have hneg := neg_le_neg hlog
  have hhalf : (-Real.logb 2 (1 / 2 : ℝ)) = (1 : ℝ) := by
    simp [Real.logb_inv]
  have h1 : (-Real.logb 2 (collProbFun f)) ≤ (-Real.logb 2 (1 / 2 : ℝ)) := by simpa using hneg
  simpa [H₂Fun, hhalf] using h1

end BoolFunc

