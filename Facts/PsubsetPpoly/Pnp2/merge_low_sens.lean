import Pnp2.Boolcube
import Pnp2.cover2
import Pnp2.family_entropy_cover

open Cover2

namespace Boolcube

/-!
`mergeLowSensitivityCover` re-exports the entropy-based cover construction
through the canonical interface `coverFamily`.  Downstream files can thus obtain
the required set of subcubes without referring to the underlying implementation
details.
-/
noncomputable def mergeLowSensitivityCover
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ)) :
  Finset (Subcube n) :=
  Cover2.coverFamily (F := F) (h := h) hH

/-- Every rectangle returned by `mergeLowSensitivityCover` is constant for each
    function of the family.  This follows directly from the corresponding
    property of `buildCover`. -/
lemma mergeLowSensitivityCover_pointwiseMono
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ))
  {C : Subcube n} (hC : C ∈ mergeLowSensitivityCover (F := F) h hH) :
  ∀ g ∈ F, Boolcube.Subcube.monochromaticFor C g := by
  classical
  have hmono :=
    Cover2.coverFamily_pointwiseMono (F := F) (h := h) (hH := hH)
  simpa [mergeLowSensitivityCover] using hmono hC

/-- All `1`-inputs of every `f ∈ F` lie in some rectangle of
    `mergeLowSensitivityCover`. -/
lemma mergeLowSensitivityCover_covers
  {n : ℕ} (F : Family n) (h : ℕ) (hH : Entropy.H₂ F ≤ (h : ℝ))
  {f : BFunc n} (hf : f ∈ F) {x : Point n} (hx : f x = true) :
  ∃ C ∈ mergeLowSensitivityCover (F := F) h hH, x ∈ₛ C := by
  classical
  have hcov := Cover2.coverFamily_spec_cover (F := F) (h := h) (hH := hH)
  simpa [mergeLowSensitivityCover] using hcov f hf x hx

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

/--
The merged cover cannot have more rectangles than the low-sensitivity cover.
This inequality is a direct consequence of `merge_card_eq_min` and is useful
when only a one-sided bound is needed.
-/
lemma merge_card_le_low_sens
    {n : ℕ} {F : Family n} {h : ℕ}
    (low_sens_cover : FamilyCover F h) (entropy_cover : FamilyCover F h) :
    (merge_cover low_sens_cover entropy_cover).rects.card ≤
      low_sens_cover.rects.card := by
  classical
  have hmin :=
    merge_card_eq_min (low_sens_cover := low_sens_cover)
      (entropy_cover := entropy_cover)
  -- Rewrite the goal using the description via `Nat.min` and apply the
  -- standard inequality `Nat.min_le_left`.
  simpa [hmin] using
    Nat.min_le_left low_sens_cover.rects.card entropy_cover.rects.card

/--
Symmetrically, the merged cover is no larger than the entropy-based one.
This lemma mirrors `merge_card_le_low_sens` and allows bounding the size from
the other side.
-/
lemma merge_card_le_entropy
    {n : ℕ} {F : Family n} {h : ℕ}
    (low_sens_cover : FamilyCover F h) (entropy_cover : FamilyCover F h) :
    (merge_cover low_sens_cover entropy_cover).rects.card ≤
      entropy_cover.rects.card := by
  classical
  have hmin :=
    merge_card_eq_min (low_sens_cover := low_sens_cover)
      (entropy_cover := entropy_cover)
  -- `Nat.min_le_right` supplies the required inequality after rewriting.
  simpa [hmin] using
    Nat.min_le_right low_sens_cover.rects.card entropy_cover.rects.card

end Boolcube
