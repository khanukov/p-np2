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

end

end BoolFunc

