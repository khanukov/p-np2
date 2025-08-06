import Pnp2.Cover.Compute

open Cover
open BoolFunc
open Boolcube

-- Silence stylistic linter warnings in this test file.
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CoverComputeTest

/-- `mBound` expands to the expected arithmetic expression. -/
example : mBound 1 0 = 2 := by
  simp [mBound]

/-- `mBound` is positive whenever `n > 0`. -/
example : 0 < mBound 1 0 := by
  simp [mBound]

/-/  `buildCoverCompute` enumerates a small cover for a trivial function. -/
def trivialFun : BoolFun 1 := fun _ => false

  example :
      (buildCoverCompute (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
        (by
          classical
          -- Collision entropy of a singleton family is zero.
          have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
          have _hH₂ := BoolFunc.H₂_card_one
              (F := ({trivialFun} : Boolcube.Family 1)) hcard
          simp)).length ≤ Fintype.card (Boolcube.Subcube 1) :=
  by
    classical
    have hspec := buildCoverCompute_spec
          (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
          (by
            have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
            have _hH₂ := BoolFunc.H₂_card_one
                (F := ({trivialFun} : Boolcube.Family 1)) hcard
            simp)
    -- The specification already yields the desired bound.
    exact hspec.2.2

/-- The list returned by `buildCoverCompute` has no duplicates. -/
example :
    (buildCoverCompute (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
      (by
        classical
        -- Collision entropy of a singleton family is zero.
        have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
        have _hH₂ := BoolFunc.H₂_card_one
            (F := ({trivialFun} : Boolcube.Family 1)) hcard
        simp)).Nodup :=
by
  classical
  have hspec := buildCoverCompute_spec
        (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
        (by
          have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
          have _hH₂ := BoolFunc.H₂_card_one
              (F := ({trivialFun} : Boolcube.Family 1)) hcard
          simp)
  exact hspec.1

end CoverComputeTest
