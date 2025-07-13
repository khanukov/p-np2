import Pnp.BoolFunc
import Pnp.Entropy
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Classical
open BoolFunc
open Finset

namespace Cover

/-! ### Numeric bound used in the main lemmas -/
@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

/-!  The full cover construction is not yet formalized.  We introduce
    axioms capturing the expected properties so that other files can
    rely on them. -/
variable {n h : ℕ} (F : Family n)

/-- All `1`-inputs of `F` lie inside some rectangle of `Rset`. -/
def AllOnesCovered (F : Family n) (Rset : Finset (Subcube n)) : Prop :=
  ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R

/-- Placeholder for the actual recursive construction of a cover. -/
noncomputable
axiom buildCover (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
  Finset (Subcube n)

axiom buildCover_mono (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
  ∀ R ∈ buildCover F h hH, Subcube.monochromaticForFamily R F

axiom buildCover_covers (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
  AllOnesCovered F (buildCover F h hH)

axiom buildCover_card_bound (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
  (buildCover F h hH).card ≤ mBound n h

/-- Existence of a good cover with the desired properties. -/
lemma cover_exists (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered F Rset ∧
      Rset.card ≤ mBound n h := by
  classical
  let Rset := buildCover (F := F) (h := h) hH
  refine ⟨Rset, ?_, ?_, ?_⟩
  · intro R hR; simpa using buildCover_mono (F := F) (h := h) (hH := hH) R hR
  · simpa using buildCover_covers (F := F) (h := h) hH
  · simpa using buildCover_card_bound (F := F) (h := h) (hH := hH)

/-- A canonical finite set of rectangles witnessing `cover_exists`. -/
noncomputable
def coverFamily (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  Classical.choose (cover_exists (F := F) (h := h) hH)

lemma coverFamily_spec (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ R ∈ coverFamily (F := F) (h := h) hH,
        Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered F (coverFamily (F := F) (h := h) hH) ∧
      (coverFamily (F := F) (h := h) hH).card ≤ mBound n h := by
  classical
  simpa [coverFamily] using
    Classical.choose_spec (cover_exists (F := F) (h := h) hH)

lemma coverFamily_mono (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ coverFamily (F := F) (h := h) hH,
      Subcube.monochromaticForFamily R F :=
  (coverFamily_spec (F := F) (h := h) hH).1

lemma coverFamily_spec_cover (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered F (coverFamily (F := F) (h := h) hH) :=
  (coverFamily_spec (F := F) (h := h) hH).2.1

lemma coverFamily_card_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (F := F) (h := h) hH).card ≤ mBound n h :=
  (coverFamily_spec (F := F) (h := h) hH).2.2

end Cover

