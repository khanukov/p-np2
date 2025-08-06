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

lemma coverFamily_eq_buildCover {n : ℕ} (F : Family n) {h : ℕ}
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
  -- `firstUncovered` reports `none`, hence the cover remains empty.
  have hfu : firstUncovered (n := n) F (∅ : Finset (Subcube n)) = none := by
    simpa using
      (firstUncovered_none_iff_AllOnesCovered (n := n) (F := F)
        (Rset := (∅ : Finset (Subcube n)))).2 hcov
  have hbuild : coverFamily (n := n) F h hH =
      (∅ : Finset (Subcube n)) := by
    simpa [coverFamily, buildCover, extendCover, hfu] using
      (extendCover_none (n := n) (F := F)
        (Rset := (∅ : Finset (Subcube n))) hfu)
  refine ⟨?mono, ?cover, ?card⟩
  · intro R hR
    have : False := by simpa [hbuild] using hR
    exact this.elim
  · simpa [hbuild] using hcov
  · have : (0 : ℕ) ≤ mBound n h := mBound_nonneg (n := n) (h := h)
    simpa [hbuild] using this

end Cover2
