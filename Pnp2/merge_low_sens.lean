import Pnp2.Boolcube
import Pnp2.cover2
import Pnp2.family_entropy_cover

open Cover2

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
  Cover2.buildCover (F := F) (h := h) hH

/-- Every rectangle returned by `mergeLowSensitivityCover` is constant for each
    function of the family.  This follows directly from the corresponding
    property of `buildCover`. -/
lemma mergeLowSensitivityCover_pointwiseMono
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ))
  {C : Subcube n} (hC : C ∈ mergeLowSensitivityCover (F := F) h hH) :
  ∀ g ∈ F, Boolcube.Subcube.monochromaticFor C g := by
  classical
  have hmono :=
    Cover2.buildCover_pointwiseMono (F := F) (h := h) (hH := hH)
  simpa [mergeLowSensitivityCover] using hmono C hC

/-- All `1`-inputs of every `f ∈ F` lie in some rectangle of
    `mergeLowSensitivityCover`. -/
lemma mergeLowSensitivityCover_covers
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ))
  {f : BFunc n} (hf : f ∈ F) {x : Point n} (hx : f x = true) :
  ∃ C ∈ mergeLowSensitivityCover (F := F) h hH, x ∈ₛ C := by
  classical
  have hcov := Cover2.buildCover_covers (F := F) (h := h) (hH := hH)
  simpa [mergeLowSensitivityCover] using hcov f hf x hx

/-- The number of rectangles produced by `mergeLowSensitivityCover` is
    bounded by `mBound`. -/
lemma mergeLowSensitivityCover_bound
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ)) :
  (mergeLowSensitivityCover (F := F) h hH).card ≤ mBound n h := by
  classical
  have hbound := Cover2.buildCover_card_bound (F := F) (h := h) (hH := hH)
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

/-!
`merge_cover` chooses the smaller of the two input covers.  Consequently the
number of rectangles in the result is the minimum of the two cardinalities.
This tiny lemma packages the case split so that downstream files can reason
about the size without repeating the definition.
-/
lemma merge_card_eq_min
    {n : ℕ} {F : Family n} {h : ℕ}
    (low_sens_cover : FamilyCover F h) (entropy_cover : FamilyCover F h) :
    (merge_cover low_sens_cover entropy_cover).rects.card =
      Nat.min low_sens_cover.rects.card entropy_cover.rects.card := by
  classical
  unfold merge_cover
  by_cases h_le : low_sens_cover.rects.card ≤ entropy_cover.rects.card
  · -- `low_sens_cover` is chosen when its cardinality is smaller.
    have hmin :
        Nat.min low_sens_cover.rects.card entropy_cover.rects.card =
          low_sens_cover.rects.card := Nat.min_eq_left h_le
    simp [merge_cover, h_le, hmin]
  · -- Otherwise `entropy_cover` wins and its size is the minimum.
    have hmin :
        Nat.min low_sens_cover.rects.card entropy_cover.rects.card =
          entropy_cover.rects.card := Nat.min_eq_right (le_of_not_le h_le)
    simp [merge_cover, h_le, hmin]

end Boolcube
