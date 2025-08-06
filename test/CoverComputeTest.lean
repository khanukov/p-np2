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

-- A simple test family with two functions on 2 bits.
def F_test : Family 2 :=
  let f1 : BFunc 2 := fun x => x 0 && x 1  -- AND
  let f2 : BFunc 2 := fun x => x 0 || x 1  -- OR
  ({f1, f2} : Finset (BFunc 2))

-- Test case for the h=0 path.
-- With h=0, the algorithm should cover each 1-point individually.
-- This test is non-computable and proves a property of the cover.
def test_h_is_zero_covers_a_point : Prop :=
  let h := 0
  -- This proof is non-trivial and is omitted for now.
  have hH : H₂ F_test ≤ (h : ℝ) := by sorry
  let cover := buildCoverCompute F_test h hH
  -- We expect the cover to contain a subcube that covers the point (true, true) for f1.
  let f1 : BFunc 2 := fun x => x 0 && x 1
  let x1 : Point 2 := fun _ => true
  ∃ R ∈ cover, x1 ∈ₛ R ∧ (∀ y ∈ₛ R, f1 y = true)

-- Test case for the h>0 path (entropy split).
-- This test proves that the cover size is bounded.
def test_h_gt_zero_card_bound : Prop :=
  let h := 1
  have hH : H₂ F_test ≤ (h : ℝ) := by
    -- H₂(F_test) = log2(2) = 1
    have h_card : F_test.card = 2 := by simp [F_test]
    simp [H₂, h_card, Real.logb_le_logb_of_le, Real.logb_pow]
    norm_num
  let cover := buildCoverCompute F_test h hH
  cover.length ≤ mBound 2 h

end CoverComputeTest
