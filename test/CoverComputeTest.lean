import Pnp2.Cover.Compute

open Cover
open BoolFunc
open Boolcube

namespace CoverComputeTest

/-- `mBound` expands to the expected arithmetic expression. -/
example : mBound 1 0 = 2 := by
  simp [mBound]

/-- `buildCoverCompute` returns the empty list for a trivial function. -/
def trivialFun : BoolFun 1 := fun _ => false

example :
    buildCoverCompute (F := ({trivialFun} : Boolcube.Family 1)) (h := 0)
      (by
        classical
        -- Collision entropy of a singleton family is zero.
        have hcard : ({trivialFun} : Boolcube.Family 1).card = 1 := by simp
        have hH₂ := BoolFunc.H₂_card_one (F := ({trivialFun} : Boolcube.Family 1)) hcard
        simpa [hH₂])
      = [] :=
by
  rfl

end CoverComputeTest
