import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

variable {α : Type} [DecidableEq α]

/--  A family `A` is `R`‑spread if for every fixed subfamily `S`
    the probability that `S ⊆ Aᵢ` is at most `R^{-|S|}`.  The
    probability is taken with respect to the uniform measure on the
    finite index. -/
def RSpread (R : ℝ) (A : Finset (Finset α)) : Prop :=
  A.Nonempty ∧
  ∀ S : Finset α,
    ((A.filter fun T ↦ S ⊆ T).card : ℝ) / A.card ≤
      Real.rpow R (-(S.card : ℝ))

lemma RSpread.mono {R₁ R₂ : ℝ} {A : Finset (Finset α)}
    (h : RSpread R₁ A) (hRR : R₂ ≤ R₁) (hpos : 0 < R₂) : RSpread R₂ A := by
  rcases h with ⟨hA, hcond⟩
  refine ⟨hA, ?_⟩
  intro S
  have hprob := hcond S
  have hz : (-(S.card : ℝ)) ≤ 0 := by
    have : 0 ≤ (S.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
    linarith
  have hmono :=
    (Real.rpow_le_rpow_of_nonpos (hx := hpos) (hxy := hRR) (hz := hz))
  exact hprob.trans hmono

lemma RSpread.card_bound {R : ℝ} {A : Finset (Finset α)}
    (h : RSpread R A) :
    ∀ S : Finset α,
      ((A.filter fun T ↦ S ⊆ T).card : ℝ) ≤
        Real.rpow R (-(S.card : ℝ)) * A.card := by
  classical
  intro S
  have hpos : (0 : ℝ) < A.card := by
    have : 0 < A.card := Finset.card_pos.mpr h.1
    exact_mod_cast this
  have hcond := h.2 S
  have := (div_le_iff₀ hpos).1 hcond
  simpa [mul_comm] using this

lemma RSpread.one_of_nonempty {A : Finset (Finset α)}
    (hA : A.Nonempty) :
    RSpread (R := 1) A := by
  classical
  refine ⟨hA, ?_⟩
  intro S
  classical
  have hsubset : (A.filter fun T ↦ S ⊆ T) ⊆ A := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hle_nat : (A.filter fun T ↦ S ⊆ T).card ≤ A.card :=
    Finset.card_mono hsubset
  have hpos_nat : 0 < A.card := Finset.card_pos.mpr hA
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast hpos_nat
  have hle_real : ((A.filter fun T ↦ S ⊆ T).card : ℝ) ≤ A.card := by
    exact_mod_cast hle_nat
  have hdiv_le :
      ((A.filter fun T ↦ S ⊆ T).card : ℝ) / A.card ≤ A.card / A.card := by
    have hnonneg : 0 ≤ (A.card : ℝ) := le_of_lt hpos
    exact div_le_div_of_nonneg_right hle_real hnonneg
  have hcard_div : (A.card : ℝ) / A.card = 1 := by
    have hne : (A.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos_nat)
    field_simp [hne]
  have hprob_le_one : ((A.filter fun T ↦ S ⊆ T).card : ℝ) / A.card ≤ 1 := by
    simpa [hcard_div] using hdiv_le
  simpa using hprob_le_one

lemma RSpread.card_filter_le {R : ℝ} {A : Finset (Finset α)}
    (h : RSpread R A) (S : Finset α) :
    ((A.filter fun T ↦ S ⊆ T).card : ℝ) ≤
      A.card * Real.rpow R (-(S.card : ℝ)) := by
  classical
  have hpos : 0 < (A.card : ℝ) := by
    have hc : 0 < A.card := Finset.card_pos.mpr h.1
    exact_mod_cast hc
  have hbound := h.2 S
  have := (div_le_iff₀ hpos).1 hbound
  simpa [mul_comm] using this
