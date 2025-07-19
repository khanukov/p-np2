import Pnp2.Boolcube
import Pnp2.cover
import Pnp2.family_entropy_cover

open Cover

namespace Boolcube

/-!
`mergeLowSensitivityCover` re-exports the entropy-based cover construction
`Cover.buildCover` so that downstream files can obtain a set of subcubes
covering all ones of `F` without referring to the full `Cover` machinery.
It takes the entropy bound as a natural number `h` and simply returns the
rectangles produced by `buildCover`.
-/
noncomputable def mergeLowSensitivityCover
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ)) :
  Finset (Subcube n) :=
  Cover.buildCover (F := F) (h := h) hH

/-- Every rectangle returned by `mergeLowSensitivityCover` is jointly
    monochromatic for the family. This follows directly from the
    corresponding property of `buildCover`. -/
lemma mergeLowSensitivityCover_mono
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ))
  {C : Subcube n} (hC : C ∈ mergeLowSensitivityCover (F := F) h hH) :
  Subcube.monochromaticForFamily C F := by
  classical
  have hmono := Cover.buildCover_mono (F := F) (h := h) (hH := hH)
  simpa [mergeLowSensitivityCover] using hmono C hC

/-- All `1`-inputs of every `f ∈ F` lie in some rectangle of
    `mergeLowSensitivityCover`. -/
lemma mergeLowSensitivityCover_covers
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ))
  {f : BFunc n} (hf : f ∈ F) {x : Point n} (hx : f x = true) :
  ∃ C ∈ mergeLowSensitivityCover (F := F) h hH, x ∈ₛ C := by
  classical
  have hcov := Cover.buildCover_covers (F := F) (h := h) (hH := hH)
  simpa [mergeLowSensitivityCover] using hcov f hf x hx

/-- The number of rectangles produced by `mergeLowSensitivityCover` is
    bounded by `mBound`. -/
lemma mergeLowSensitivityCover_bound
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ)) :
  (mergeLowSensitivityCover (F := F) h hH).card ≤ mBound n h := by
  classical
  have hbound := Cover.buildCover_card_bound (F := F) (h := h) (hH := hH)
  simpa [mergeLowSensitivityCover] using hbound

/-- Choose the smaller of a low-sensitivity and an entropy-based cover. -/
noncomputable def merge_cover
    {n : ℕ} {F : Family n} {h : ℕ}
    (low_sens_cover : FamilyCover F h) (entropy_cover : FamilyCover F h) :
    FamilyCover F h :=
  if low_sens_cover.rects.card ≤ entropy_cover.rects.card then
    low_sens_cover
  else
    entropy_cover

/-- The merged cover still covers all `1`-inputs of the family. -/
lemma merge_correct
    {n : ℕ} {F : Family n} {h : ℕ}
    (low_sens_cover : FamilyCover F h) (entropy_cover : FamilyCover F h) :
    AllOnesCovered F (merge_cover low_sens_cover entropy_cover).rects := by
  classical
  unfold merge_cover
  by_cases h_le : low_sens_cover.rects.card ≤ entropy_cover.rects.card
  · simpa [merge_cover, h_le] using low_sens_cover.covers
  · simpa [merge_cover, h_le] using entropy_cover.covers

end Boolcube
