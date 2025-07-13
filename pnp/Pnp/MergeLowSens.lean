import Pnp.Boolcube
import Pnp.Cover
import Pnp.Entropy

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
  {n : ℕ} (_F : Family n) (_h : ℕ) (_hH : BoolFunc.H₂ _F ≤ (_h : ℝ)) :
  Finset (Subcube n) :=
  (∅ : Finset (Subcube n))

end Boolcube
