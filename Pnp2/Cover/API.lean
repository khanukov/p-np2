import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.cover

namespace Cover.API

open Cover

variable {n : ℕ} {h : ℕ} {F : Family n}
variable (hH : BoolFunc.H₂ F ≤ (h : ℝ))

/--
`rectangles` enumerates the cover for `F` provided by `Cover.coverFamily`.
It is defined as an abbreviation so that downstream files can use the
constructive enumerator without importing the full `Cover` module.
-/
abbrev rectangles : Finset (Subcube n) :=
  coverFamily (F := F) (h := h) hH

/--
Every rectangle in `rectangles hH` is monochromatic for the family `F`.
This property is re-exported from `Cover` so that `Cover.Compute` can
use it without depending on the large definitions in `cover.lean`.
-/
lemma mono :
    ∀ R ∈ rectangles (F := F) (h := h) hH, Subcube.monochromaticForFamily R F :=
  coverFamily_mono (F := F) (h := h) hH

/--
The number of rectangles returned by `rectangles` is bounded by `mBound`.
This numeric bound is critical for the SAT algorithms that iterate over
the cover.
-/
lemma card_bound :
    (rectangles (F := F) (h := h) hH).card ≤ mBound n h :=
  coverFamily_card_bound (F := F) (h := h) hH

end Cover.API
