import Pnp2.cover2

/-!
# Canonical cover family

This module packages the convenience wrapper `coverFamily` around the
`buildCover` construction from `cover2.lean`.  The current development uses
`buildCover` as a stub that simply returns the input set of rectangles, but the
API is structured to mirror the eventual proof.

The definitions and lemmas below are heavily documented so that the role of
`coverFamily` remains clear even in this simplified environment.
-/

namespace Cover2

open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

/--
`coverFamily F h hH` produces a canonical set of rectangles covering the
Boolean family `F` with collision-entropy budget `h`.  At the moment the
implementation simply delegates to `buildCover`, but exposing this definition
in its own module keeps the interface stable during refactoring.
-/
noncomputable def coverFamily {n : ℕ} (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  buildCover (n := n) F h hH

@[simp] lemma coverFamily_eq_buildCover {n : ℕ} (F : Family n) {h : ℕ}
    (_hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    coverFamily (n := n) F h _hH = buildCover (n := n) F h _hH := rfl

/--
Basic specification for the canonical cover.  Every rectangle is
monochromatic, all `1`-inputs are covered and the size is bounded by `mBound`.
-/
lemma coverFamily_spec {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    (∀ R ∈ coverFamily (n := n) F h hH,
        Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered (n := n) F (coverFamily (n := n) F h hH) ∧
      (coverFamily (n := n) F h hH).card ≤ mBound n h := by
  classical
  refine ⟨?mono, ?cover, ?card⟩
  · -- Monochromaticity follows from the underlying `buildCover` lemma.
    simpa [coverFamily] using
      (buildCover_mono (n := n) (F := F) (h := h) hH)
  · -- Coverage relies on the hypothesis that the empty set already covers
    -- all `1`-inputs.  With the stubbed `buildCover` the set stays empty.
    simpa [coverFamily] using
      (buildCover_covers (n := n) (F := F) (h := h) hH hcov)
  · -- The cardinality bound comes directly from `buildCover`.
    simpa [coverFamily] using
      (buildCover_card_bound (n := n) (F := F) (h := h) hH)

/--
`coverFamily_spec` specialised to the coverage property.
-/
lemma coverFamily_spec_cover {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hcov : AllOnesCovered (n := n) F (∅ : Finset (Subcube n))) :
    AllOnesCovered (n := n) F (coverFamily (n := n) F h hH) :=
  (coverFamily_spec (n := n) (F := F) (h := h) hH hcov).2.1

/--
Every rectangle in the canonical cover is monochromatic for the family.
-/
lemma coverFamily_mono {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ coverFamily (n := n) F h hH,
      Subcube.monochromaticForFamily R F := by
  -- Unfold `coverFamily` and reuse the corresponding lemma for `buildCover`.
  simpa [coverFamily] using
    (buildCover_mono (n := n) (F := F) (h := h) hH)

/--
Cardinality bound for the canonical cover expressed via `mBound`.
-/
lemma coverFamily_card_bound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) F h hH).card ≤ mBound n h := by
  simpa [coverFamily] using
    (buildCover_card_bound (n := n) (F := F) (h := h) hH)

/--
A coarse linear bound on the size of the canonical cover.
-/
lemma coverFamily_card_linear_bound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) F h hH).card ≤ 2 * h + n := by
  simpa [coverFamily] using
    (buildCover_card_linear_bound (n := n) (F := F) (h := h) hH)

/--
Universal bound on the size of the canonical cover.
-/
lemma coverFamily_card_univ_bound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) F h hH).card ≤ bound_function n := by
  simpa [coverFamily] using
    (buildCover_card_univ_bound (n := n) (F := F) (h := h) hH)

end Cover2
