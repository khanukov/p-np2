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
Boolean family `F` with collision-entropy budget `h`.  It is defined as the
`buildCover` construction from `Cover.BuildCover` and therefore inherits all
structural properties and bounds proved for that recursion.  The separate wrapper
keeps the downstream API lightweight while we continue to refine the cover
machinery.
-/
noncomputable def coverFamily {n : ℕ} (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  buildCover (n := n) F h hH

/--
Basic specification for the canonical cover.  Every rectangle is
monochromatic, all `1`-inputs are covered and the number of rectangles
is bounded by the total number of subcubes.
-/
lemma coverFamily_spec {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ R ∈ coverFamily (n := n) F h hH,
        ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g) ∧
      AllOnesCovered (n := n) F (coverFamily (n := n) F h hH) ∧
      (coverFamily (n := n) F h hH).card ≤
        2 ^ n := by
  classical
  refine ⟨?mono, ?covers, ?bound⟩
  · intro R hR g hg
    exact buildCover_pointwiseMono (F := F) (h := h) (hH := hH) R hR g hg
  · exact buildCover_covers (F := F) (h := h) (hH := hH)
  · exact buildCover_card_bound (n := n) (F := F) (h := h) hH

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
The canonical cover also satisfies the explicit size bound.
-/
lemma coverFamily_spec_bound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
      (coverFamily (n := n) F h hH).card ≤
      2 ^ n :=
  (coverFamily_spec (n := n) (h := h) (F := F) hH).2.2

/--
`coverFamily_spec` can be strengthened to the explicit `mBound` cardinality
estimate once an external numeric argument shows that `mBound n h` dominates
the total number of subcubes.  This separates the combinatorial cover
construction from the arithmetic reasoning about the size bound.
-/
lemma coverFamily_spec_mBound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hn : 0 < n) :
    (∀ R ∈ coverFamily (n := n) F h hH,
        ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g) ∧
      AllOnesCovered (n := n) F (coverFamily (n := n) F h hH) ∧
      (coverFamily (n := n) F h hH).card ≤ mBound n h := by
  classical
  -- Start from the basic specification and strengthen the cardinality bound.
  obtain hspec := coverFamily_spec (n := n) (h := h) (F := F) hH
  refine ⟨hspec.1, hspec.2.1, ?_⟩
  -- Rewrite `coverFamily` as `buildCover` to reuse the strengthened bound.
  simpa [coverFamily]
    using (buildCover_card_le_mBound (n := n) (F := F) (h := h)
      (hH := hH) hn)

/-- Convenience wrapper extracting only the cardinality estimate from
`coverFamily_spec_mBound`.  This form is handy when the other properties are
already known or irrelevant for the caller. -/
lemma coverFamily_card_le_mBound {n h : ℕ} (F : Family n)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hn : 0 < n) :
    (coverFamily (n := n) F h hH).card ≤ mBound n h :=
  (coverFamily_spec_mBound (n := n) (h := h) (F := F) hH hn).2.2

end Cover2
