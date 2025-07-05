import Mathlib.Probability
import Mathlib.Data.Finset.Card

open Finset

variable {α : Type} [DecidableEq α]

/--  Семейство `A` рассеяно (`R`‑spread), если
     для любой фиксированной подсемьи `S` вероятность
     `S ⊆ Aᵢ` не превосходит `R^{-|S|}`.  Здесь вероятность
     задаётся равномерной мерой на конечном индексе. -/
def RSpread (R : ℝ) (A : Finset (Finset α)) : Prop :=
  A.Nonempty ∧
  ∀ S : Finset α,
    ((A.filter fun T ↦ S ⊆ T).card : ℝ) / A.card ≤ R ^ (-(S.card : ℝ))

lemma RSpread.mono  {R₁ R₂ : ℝ} {A : Finset (Finset α)}
    (h : RSpread R₁ A) (hRR : R₁ ≤ R₂) : RSpread R₂ A := by
  rcases h with ⟨hA, hcond⟩
  refine ⟨hA, ?_⟩
  intro S
  have := hcond S
  calc
    ((A.filter _).card : ℝ) / A.card ≤ R₁ ^ (-(S.card : ℝ)) := this
    _ ≤ R₂ ^ (-(S.card : ℝ)) := by
      have hpow : (-(S.card : ℝ)) ≤ 0 := by
        have : 0 ≤ (S.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
        linarith
      gcongr
      exact hRR

