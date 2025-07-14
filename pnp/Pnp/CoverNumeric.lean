import Pnp.FamilyEntropyCover
import Pnp.Entropy
import Pnp.Bound

open BoolFunc

namespace CoverNumeric

variable {N Nδ : ℕ} (F : Family N)

/-- Collision entropy is bounded by the family size. -/
lemma H₂_le_card : BoolFunc.H₂ F ≤ F.card := by
  classical
  by_cases hF : F.card = 0
  · simp [BoolFunc.H₂, hF]
  ·
    have hb : (1 : ℝ) < 2 := by norm_num
    have hpos : 0 < (F.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hF
    have hpow : (F.card : ℝ) ≤ (2 : ℝ) ^ F.card := by
      have hpow_nat : F.card ≤ 2 ^ F.card :=
        Nat.le_of_lt (Nat.lt_two_pow_self _)
      exact_mod_cast hpow_nat
    have hlog :=
      Real.logb_le_logb_of_le (hb := hb) hpos hpow
    have hpow' : Real.logb 2 ((2 : ℝ) ^ F.card) = F.card := by
      have hbpos : (0 : ℝ) < 2 := by norm_num
      have hbne : (2 : ℝ) ≠ 1 := by norm_num
      simpa using Real.logb_pow hbpos hbne hpos
    simpa [BoolFunc.H₂, hpow'] using hlog

/-- Minimal size of a cover for `F`. -/
noncomputable def minCoverSize (F : Family N) : ℕ :=
  Nat.find (by
    classical
    let FC := Boolcube.familyEntropyCover (F := F) (h := F.card)
      (H₂_le_card (F := F))
    refine ⟨FC.rects.card, ?_⟩
    exact ⟨FC.rects, ⟨FC.mono, FC.covers⟩, rfl⟩)

/-- A helper lemma: the minimal cover is no larger than any particular cover. -/
lemma minCoverSize_le_of_cover {Rset : Finset (BoolFunc.Subcube N)}
    (hR : (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R)) :
    minCoverSize F ≤ Rset.card := by
  classical
  let P k := ∃ R : Finset (BoolFunc.Subcube N),
      (∀ R' ∈ R, Subcube.monochromaticForFamily R' F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R' ∈ R, x ∈ₛ R') ∧ R.card = k
  have hex : ∃ k, P k :=
    by
      simpa [P, minCoverSize] using (Nat.find_spec (by
        classical
        let FC := Boolcube.familyEntropyCover (F := F) (h := F.card)
          (H₂_le_card (F := F))
        refine ⟨FC.rects.card, ?_⟩
        exact ⟨FC.rects, FC.mono, FC.covers, rfl⟩))
  have hR' : P Rset.card := ⟨Rset, hR.1, hR.2, rfl⟩
  simpa [minCoverSize, P] using
    Nat.find_min' hex hR'

/-- Entropy-based size bound for a family cover. -/
lemma buildCover_size_bound
    (h₀ : BoolFunc.H₂ F ≤ N - Nδ)
    (hn : N ≥ Bound.n₀ (N - Nδ)) :
    minCoverSize F ≤ 2 ^ (N - Nδ) := by
  classical
  obtain ⟨Rset, hmono, hcov, hcard⟩ :=
    Bound.family_collision_entropy_lemma (F := F) (h := N - Nδ)
      (hH := h₀) (hn := hn)
  have hcover :
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) :=
    ⟨hmono, hcov⟩
  have hmin := minCoverSize_le_of_cover (F := F) hcover
  exact hmin.trans hcard

lemma numeric_bound
    (h₀ : BoolFunc.H₂ F ≤ N - Nδ)
    (hn : N ≥ Bound.n₀ (N - Nδ)) :
    minCoverSize F ≤ 2 ^ (N - Nδ) := by
  simpa using buildCover_size_bound (F := F) (Nδ := Nδ) h₀ hn

end CoverNumeric
