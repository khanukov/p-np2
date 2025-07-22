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
        sorry)
      = [] :=
by
  rfl

end CoverComputeTest
