import Pnp.Boolcube
import Pnp.Cover
import Pnp.Entropy
import Pnp.FamilyEntropyCover

open Cover
open BoolFunc

namespace Boolcube

/-!
`mergeLowSensitivityCover` simply re-exports the entropy-based cover
construction `Cover.buildCover` so that downstream files can obtain a
set of subcubes covering all ones of `F` without referring to the full
`Cover` infrastructure.  It takes the entropy bound as a natural number
`h` and returns the list of rectangles produced by `buildCover`.
-/
noncomputable def mergeLowSensitivityCover
  {n : ℕ} (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
  Finset (BoolFunc.Subcube n) :=
  (familyEntropyCover (F := F) (h := h) hH).rects

end Boolcube
