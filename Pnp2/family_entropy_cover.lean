import Pnp2.Boolcube
import Pnp2.cover2
import Pnp2.Cover.Canonical
import Pnp2.entropy

namespace Boolcube

open Entropy
open Cover2

/-!
`familyCollisionEntropyCover` wraps the existential statement
`Cover2.cover_exists` for easier use in downstream files.  It asserts that a
family of Boolean functions with bounded collision entropy admits a small set of
subcubes that are monochromatic for every function in the family when inspected
pointwise.  The full proof is nontrivial and omitted; this declaration merely
re‑exports the existential lemma so that other parts of the development can rely
on it.
-/
theorem familyCollisionEntropyCover
  {n : ℕ} (F : Family n) {h : ℕ} (hH : H₂ F ≤ (h : ℝ)) :
  ∃ (T : Finset (Subcube n)),
    (∀ C ∈ T, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor C g) ∧
    (∀ f ∈ F, ∀ x, f x = true → ∃ C, C ∈ T ∧ C.Mem x) := by
  classical
  simpa using Cover2.cover_exists (F := F) (h := h) hH

/-!
### A convenience record for covers returned by `familyEntropyCover`.
This bundles the list of rectangles together with proofs that each is
monochromatic for the whole family, that the rectangles cover all
`1`‑inputs, and an explicit bound on their number.  The size bound is
parametrised by `mBound n h`, the coarse upper estimate used throughout the
cover development.  An external arithmetic argument must establish that this
quantity indeed dominates the total number of subcubes; see
`coverFamily_card_le_mBound` for the combinatorial part of the story.
-/
structure FamilyCover {n : ℕ} (F : Family n) (h : ℕ) where
  /-- The covering rectangles. -/
  rects   : Finset (Subcube n)
  /-- Each rectangle is monochromatic for every function of the family. -/
  mono    : ∀ C ∈ rects, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor C g
  /-- Every `1`-input of every function is contained in some rectangle. -/
  covers  : ∀ f ∈ F, ∀ x, f x = true → ∃ C ∈ rects, x ∈ₛ C
  /-- Cardinality bound exposed via the explicit quantity `mBound`. -/
  bound   : rects.card ≤ Cover2.mBound n h

/--
`familyEntropyCover` packages the canonical cover produced by `coverFamily` into
an explicit record exposing its basic properties.  The construction relies on
classical choice and is therefore non‑computable, but it provides a convenient
interface for downstream modules.
-/
noncomputable def familyEntropyCover
    {n : ℕ} (F : Family n) {h : ℕ}
    (hH : H₂ F ≤ (h : ℝ))
    (hn : 0 < n) :
    FamilyCover F h := by
  classical
  -- NOTE: The `hlarge` parameter was removed as it led to a contradiction.
  -- The underlying `buildCover_card_le_mBound` now provides the bound
  -- without this restrictive assumption.
  refine
    ⟨Cover2.buildCover (F := F) (h := h) hH,
      ?mono, ?covers, ?bound⟩
  · -- Monochromaticity is inherited from `buildCover`.
    intro C hC g hg
    exact Cover2.buildCover_pointwiseMono (F := F) (h := h) (hH := hH) C hC g hg
  · -- All `1`-inputs are covered by construction.
    intro f hf x hx
    exact Cover2.buildCover_covers (F := F) (h := h) (hH := hH) f hf x hx
  · -- Cardinality bound supplied by `buildCover`.
    exact Cover2.buildCover_card_le_mBound
      (F := F) (h := h) (hH := hH) hn

/-!
`familyEntropyCover` is defined using `buildCover`. The following lemma
exposes this relationship by identifying the set of rectangles produced by
both constructions. This convenience result simplifies linking the wrapper
record with the underlying cover used elsewhere in the development.
-/
@[simp] lemma familyEntropyCover_rects_eq_buildCover
    {n : ℕ} (F : Family n) {h : ℕ}
    (hH : H₂ F ≤ (h : ℝ))
    (hn : 0 < n) :
    (familyEntropyCover (F := F) (h := h) hH hn).rects
      = Cover2.buildCover (F := F) (h := h) hH := by
  simp [familyEntropyCover]

end Boolcube

open Boolcube

/--
`entropyCover` translates a bound on the integer measure of `F` into an
explicit cover whose size does not exceed the total number of subcubes.  Each
subcube is monochromatic for every function in `F`, and together they cover all
`1`-inputs of the family.
-/
lemma entropyCover {n : ℕ} (F : Family n) {h : ℕ} :
    BoolFunc.measure F ≤ h →
    0 < n →
    ∃ R : Finset (Subcube n),
      (∀ C ∈ R, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor C g) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ C ∈ R, x ∈ₛ C) ∧
      R.card ≤ Cover2.mBound n h := by
  intro hμ hn
  classical
  -- Translate the measure bound into a real entropy bound.
  have hH : BoolFunc.H₂ F ≤ (h : ℝ) :=
    BoolFunc.H₂_le_of_measure_le (F := F) (h := h) hμ
  -- Package the canonical cover with all required properties.
  let FC := familyEntropyCover (F := F) (h := h) hH hn
  exact ⟨FC.rects, FC.mono, FC.covers, FC.bound⟩
