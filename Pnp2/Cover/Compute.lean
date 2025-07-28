import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.Cover.API

open Cover.API BoolFunc

namespace Cover

variable {n : ℕ} {h : ℕ} {F : Family n}
variable (hH : BoolFunc.H₂ F ≤ (h : ℝ))

/--
`buildCoverCompute` enumerates the rectangles produced by `Cover.coverFamily`.
It simply converts the finite set of rectangles into a list.
The implementation avoids importing the heavy `Cover` module directly
by relying on the thin API re-exported in `Cover.API`.
-/
noncomputable def buildCoverCompute : List (Subcube n) :=
  (rectangles (F := F) (h := h) hH).toList

@[simp] lemma buildCoverCompute_toFinset :
    (buildCoverCompute (F := F) (h := h) hH).toFinset =
      rectangles (F := F) (h := h) hH := by
  simp [buildCoverCompute]

/--
Every rectangle returned by `buildCoverCompute` is monochromatic for `F`,
and the length of the list is bounded by `mBound`.
-/
lemma buildCoverCompute_spec :
    (∀ R ∈ (buildCoverCompute (F := F) (h := h) hH).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤ mBound n h := by
  classical
  have hmono := mono (F := F) (h := h) hH
  have hcard := card_bound (F := F) (h := h) hH
  constructor
  · intro R hR; simpa [buildCoverCompute_toFinset] using hmono R hR
  ·
    have hlen : (buildCoverCompute (F := F) (h := h) hH).length =
        (rectangles (F := F) (h := h) hH).card := by
      simp [buildCoverCompute]
    simpa [hlen] using hcard

end Cover
