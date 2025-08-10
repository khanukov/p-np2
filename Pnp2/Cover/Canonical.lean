import Pnp2.cover2

/-!
# Canonical cover family

This module packages the convenience wrapper `coverFamily` around the
`buildCover` construction from `cover2.lean`.  The API mirrors the eventual
full proof even though some lemmas are currently provided as placeholders.

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
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ R ∈ coverFamily (n := n) F h hH,
        ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g) ∧
      AllOnesCovered (n := n) F (coverFamily (n := n) F h hH) ∧
      (coverFamily (n := n) F h hH).card ≤ mBound n h := by
  classical
  unfold coverFamily
  refine ⟨?mono, ?covers, ?bound⟩
  · intro R hR g hg
    have hmono :=
      buildCover_pointwiseMono (n := n) (F := F) (h := h) (hH := hH)
    exact hmono R hR g hg
  · exact buildCover_covers (n := n) (F := F) (h := h) (hH := hH)
  · exact buildCover_card_bound (n := n) (F := F) (h := h) (hH := hH)

/--
Every rectangle returned by `coverFamily` is monochromatic for the input family.
This lemma unwraps the first component of `coverFamily_spec` for convenient use
in downstream developments.
-/
lemma coverFamily_pointwiseMono {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {R : Subcube n} (hR : R ∈ coverFamily (n := n) F h hH) :
    ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g :=
  (coverFamily_spec (n := n) (h := h) (F := F) hH).1 R hR

/--
The canonical cover produced by `coverFamily` covers every `1`-input of the
family.  This is the second component of `coverFamily_spec`.
-/
lemma coverFamily_spec_cover {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered (n := n) F (coverFamily (n := n) F h hH) :=
  (coverFamily_spec (n := n) (h := h) (F := F) hH).2.1

/--
The number of rectangles in `coverFamily` never exceeds `mBound`.  This is the
third component of `coverFamily_spec`.
-/
lemma coverFamily_card_bound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) F h hH).card ≤ mBound n h :=
  (coverFamily_spec (n := n) (h := h) (F := F) hH).2.2

end Cover2
