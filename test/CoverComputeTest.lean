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
        simp)
      ).length ≤ mBound 1 0 :=
by
  classical
  have hspec := buildCoverCompute_spec
        (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
        (by
          have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
          have _hH₂ := BoolFunc.H₂_card_one
              (F := ({trivialFun} : Boolcube.Family 1)) hcard
          simp)
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

open Cover2

/-- `buildCoverCompute` enumerates the same rectangles as `Cover2.buildCover`. -/
example :
    (buildCoverCompute (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
      (by
        have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
        simpa [hcard] using
          (BoolFunc.H₂_card_one
            (F := ({trivialFun} : Boolcube.Family 1)) hcard))).toFinset =
      Cover2.buildCover (n := 1) ({trivialFun} : Boolcube.Family 1) 0
        (by
          have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
          simpa [hcard] using
            (BoolFunc.H₂_card_one
              (F := ({trivialFun} : Boolcube.Family 1)) hcard)) :=
by
  classical
  simpa using
    (buildCoverCompute_toFinset
      (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
      (by
        have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
        simpa [hcard] using
          (BoolFunc.H₂_card_one
            (F := ({trivialFun} : Boolcube.Family 1)) hcard)))

/-- `buildCoverCompute` returns the empty list precisely when the underlying
`Cover2.buildCover` set is empty.  This sanity check uses the stubbed cover,
which always yields no rectangles for the trivial family. -/
example :
    buildCoverCompute (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
      (by
        have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
        simpa [hcard] using
          (BoolFunc.H₂_card_one
            (F := ({trivialFun} : Boolcube.Family 1)) hcard)) = [] := by
  classical
  -- Prepare the entropy bound once more for reuse.
  have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
  have hH : BoolFunc.H₂ ({trivialFun} : Boolcube.Family 1) ≤ (0 : ℝ) := by
    simpa using
      (BoolFunc.H₂_card_one (F := ({trivialFun} : Boolcube.Family 1)) hcard)
  -- The stubbed cover construction yields the empty set of rectangles.
  have hset :=
    Cover2.buildCover_eq_Rset
      (n := 1) (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
      (_hH := by simpa using hH)
      (Rset := (∅ : Finset (Boolcube.Subcube 1)))
  -- Apply the characterisation lemma from `Cover.Compute`.
  exact
    (buildCoverCompute_nil_iff
      (n := 1) (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
      (by simpa using hH)).2
      (by simpa using hset)

end CoverComputeTest
