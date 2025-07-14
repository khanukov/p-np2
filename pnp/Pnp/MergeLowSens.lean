import Pnp.Boolcube
import Pnp.Cover
import Pnp.Entropy
import Pnp.FamilyEntropyCover

open Cover
open BoolFunc

namespace Boolcube

/-!
`mergeLowSensitivityCover` simply re-exports the entropy-based cover
construction provided by `familyEntropyCover`.  Downstream files can
obtain a set of subcubes covering all ones of `F` without referring to
the full `Cover` infrastructure.  It takes the entropy bound as a natural
number `h` and returns the list of rectangles produced by
`familyEntropyCover`.
-/
noncomputable def mergeLowSensitivityCover
  {n : ℕ} (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
  Finset (BoolFunc.Subcube n) :=
  (familyEntropyCover (F := F) (h := h) hH).rects

lemma mergeLowSensitivityCover_mono
    {n : ℕ} (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {C : BoolFunc.Subcube n} (hC : C ∈ mergeLowSensitivityCover (F := F) h hH) :
    BoolFunc.Subcube.monochromaticForFamily C F := by
  classical
  have := (familyEntropyCover (F := F) (h := h) hH).mono
  simpa [mergeLowSensitivityCover] using this C hC

lemma mergeLowSensitivityCover_covers
    {n : ℕ} (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {f : BoolFunc.BFunc n} (hf : f ∈ F) {x : BoolFunc.Point n}
    (hx : f x = true) :
    ∃ C ∈ mergeLowSensitivityCover (F := F) h hH, x ∈ₛ C := by
  classical
  have := (familyEntropyCover (F := F) (h := h) hH).covers
  simpa [mergeLowSensitivityCover] using this f hf x hx

lemma mergeLowSensitivityCover_bound
    {n : ℕ} (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (mergeLowSensitivityCover (F := F) h hH).card ≤ mBound n h := by
  classical
  have := (familyEntropyCover (F := F) (h := h) hH).bound
  simpa [mergeLowSensitivityCover] using this

end Boolcube
