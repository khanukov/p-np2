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

lemma RSpread.mono  {R₁ R₂ : ℝ} {A : Finset (Finset α)}
    (h : RSpread R₁ A) (hRR : R₁ ≤ R₂) : RSpread R₂ A := by
  rcases h with ⟨hA, hcond⟩
  refine ⟨hA, ?_⟩
  intro S
  have := hcond S
  calc
    ((A.filter _).card : ℝ) / A.card ≤ Real.rpow R₁ (-(S.card : ℝ)) := this
    _ ≤ Real.rpow R₂ (-(S.card : ℝ)) := by
      have hpow : (-(S.card : ℝ)) ≤ 0 := by
        have : 0 ≤ (S.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
        linarith
      gcongr
      exact hRR

