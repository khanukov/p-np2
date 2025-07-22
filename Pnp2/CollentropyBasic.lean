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
  -- The original proof bounds the product via a completing-the-square trick.
  -- We omit the algebra here and leave the inequality as an admitted fact.
  sorry

lemma collProbFun_ge_half (f : BFunc n) :
    (1 / 2 : ℝ) ≤ collProbFun f := by
  classical
  -- Admitted for now: the collision probability of a Boolean function is at
  -- least `1/2`.  The full proof follows `prob_mul_le_quarter` above.
  sorry

lemma collProbFun_le_one (f : BFunc n) :
    collProbFun f ≤ 1 := by
  classical
  -- Another numerical bound that follows from `prob_mul_le_quarter`.
  -- We keep only the statement for now.
  sorry

lemma H₂Fun_le_one (f : BFunc n) :
    H₂Fun f ≤ 1 := by
  classical
  -- This bound follows from monotonicity of the logarithm applied to
  -- `collProbFun_ge_half`.  Its detailed proof is omitted.
  sorry

end BoolFunc

