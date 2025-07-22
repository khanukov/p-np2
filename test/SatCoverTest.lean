import Pnp2.Algorithms.SatCover

open Pnp2.Algorithms
open Boolcube

namespace SatCoverTest

/-- Simple 3-bit OR function. -/
def or3 : BoolFun 3 := fun x => x 0 || x 1 || x 2

/-- Simple 3-bit AND function. -/
def and3 : BoolFun 3 := fun x => x 0 && x 1 && x 2

/-- Constantly false function. -/
def const0 : BoolFun 3 := fun _ => false

/-- `satViaCover` finds a witness for `or3`. -/
example : ∃ x, satViaCover (n := 3) or3 1 = some x ∧ or3 x = true := by
  classical
  have hx : ∃ x, or3 x = true := by
    refine ⟨fun _ => true, ?_⟩
    simp [or3]
  have hcorrect := (satViaCover_correct (f := or3) (h := 1)).mpr hx
  exact hcorrect

/-- `satViaCover` finds a witness for `and3`. -/
example : ∃ x, satViaCover (n := 3) and3 1 = some x ∧ and3 x = true := by
  classical
  have hx : ∃ x, and3 x = true := by
    refine ⟨fun _ => true, ?_⟩
    simp [and3]
  have hcorrect := (satViaCover_correct (f := and3) (h := 1)).mpr hx
  exact hcorrect

/-- The constantly false function yields `none`. -/
example : satViaCover (n := 3) const0 1 = none := by
  classical
  have hnone := (satViaCover_none (f := const0) (h := 1)).mpr (by intro x; simp [const0])
  simpa using hnone

end SatCoverTest

