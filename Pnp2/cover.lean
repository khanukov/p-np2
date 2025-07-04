import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Agreement

open Classical
open BoolFunc
open Agreement

namespace Cover

/-! ### Numeric bound -/

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

lemma numeric_bound (n h : ℕ) : 2 * h + n ≤ mBound n h := by
  classical
  -- Proof omitted
  sorry

/-! ### Main cover existence lemma -/

lemma cover_exists {n h : ℕ} (F : Family n)
    (hH : H₂ F ≤ (h : ℝ)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, R.monochromaticForFamily F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ mBound n h := by
  classical
  -- Proof omitted
  sorry

/-- Choose a specific cover using classical choice. -/
noncomputable
def coverFamily {n h : ℕ} (F : Family n)
    (hH : H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  Classical.choose (cover_exists (F := F) (h := h) hH)

@[simp] lemma coverFamily_spec_mono
    {n h : ℕ} {F : Family n} (hH : H₂ F ≤ (h : ℝ)) :
    ∀ R, R ∈ coverFamily (n := n) (h := h) F hH →
      R.monochromaticForFamily F := by
  classical
  -- Proof omitted
  sorry

@[simp] lemma coverFamily_spec_cover
    {n h : ℕ} {F : Family n} (hH : H₂ F ≤ (h : ℝ)) :
    ∀ f ∈ F, ∀ x, f x = true →
      ∃ R, R ∈ coverFamily (n := n) (h := h) F hH ∧ x ∈ₛ R := by
  classical
  -- Proof omitted
  sorry

@[simp] lemma coverFamily_card_bound
    {n h : ℕ} {F : Family n} (hH : H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := n) (h := h) F hH).card ≤ mBound n h := by
  classical
  -- Proof omitted
  sorry

end Cover
