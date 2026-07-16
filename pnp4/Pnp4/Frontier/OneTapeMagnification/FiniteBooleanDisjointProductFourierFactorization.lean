import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fourier factorization of disjoint local products

The masked-product identity has an exact coefficient-level consequence.  If
the factors depend on pairwise-disjoint coordinate sets, then every Fourier
support inside their union splits uniquely across those sets and the global
coefficient is the product of the corresponding local coefficients.  A
coefficient whose support leaves the advertised union is zero.

This is a finite identity over `Rat`; it assumes no pseudorandom generator or
Fourier-growth estimate.
-/

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanMaskedProductFactorization

namespace FiniteBooleanDisjointProductFourierFactorization

/-- Uniform averaging of a product of functions on pairwise-disjoint supports
factors exactly.  This is the all-live specialization of the masked-product
identity. -/
theorem finiteAverage_finset_prod_eq_prod
    {n : Nat} {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (support : Index → Finset (Fin n))
    (factor : Index → (Fin n → Bool) → Rat)
    (hlocal : ∀ index ∈ indices,
      DependsOnlyOn (support index) (factor index))
    (hdisjoint : ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right →
      Disjoint (support left) (support right)) :
    finiteAverage (fun input : Fin n → Bool =>
        ∏ index ∈ indices, factor index input) =
      ∏ index ∈ indices, finiteAverage (factor index) := by
  have hmasked (uniform : Fin n → Bool) :
      maskedInput (fun _ : Fin n => false) (fun _ : Fin n => true) uniform =
        uniform := by
    funext coordinate
    simp only [maskedInput, Bool.true_and, Bool.false_xor]
  simpa only [hmasked] using
    (finiteAverage_finset_prod_maskedInput_eq_prod
      indices support factor hlocal hdisjoint
      (fun _ : Fin n => false) (fun _ : Fin n => true))

/-- Exact Fourier coefficient of a disjoint local product, provided the
requested frequency is contained in the union of the advertised supports. -/
theorem coefficient_finset_prod_eq_prod_inter_of_subset
    {n : Nat} {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (support : Index → Finset (Fin n))
    (factor : Index → (Fin n → Bool) → Rat)
    (hlocal : ∀ index ∈ indices,
      DependsOnlyOn (support index) (factor index))
    (hdisjoint : ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right →
      Disjoint (support left) (support right))
    (frequency : Finset (Fin n))
    (hfrequency : frequency ⊆ indices.biUnion support) :
    coefficient
        (fun input : Fin n → Bool =>
          ∏ index ∈ indices, factor index input)
        frequency =
      ∏ index ∈ indices,
        coefficient (factor index) (frequency ∩ support index) := by
  classical
  let piece : Index → Finset (Fin n) := fun index =>
    frequency ∩ support index
  have hpiecePairwise :
      Set.PairwiseDisjoint (↑indices) piece := by
    intro left hleft right hright hne
    exact (hdisjoint left hleft right hright hne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hcover : indices.biUnion piece = frequency := by
    ext coordinate
    simp only [Finset.mem_biUnion, piece, Finset.mem_inter]
    constructor
    · rintro ⟨index, _hindex, hfrequencyCoordinate, _hsupport⟩
      exact hfrequencyCoordinate
    · intro hfrequencyCoordinate
      have hunion := hfrequency hfrequencyCoordinate
      simp only [Finset.mem_biUnion] at hunion
      obtain ⟨index, hindex, hsupport⟩ := hunion
      exact ⟨index, hindex, hfrequencyCoordinate, hsupport⟩
  have hcharacter (input : Fin n → Bool) :
      character frequency input =
        ∏ index ∈ indices, character (piece index) input := by
    unfold character
    rw [← hcover]
    exact Finset.prod_biUnion hpiecePairwise
  let twisted : Index → (Fin n → Bool) → Rat := fun index input =>
    factor index input * character (piece index) input
  have htwistedLocal : ∀ index ∈ indices,
      DependsOnlyOn (support index) (twisted index) := by
    intro index hindex
    have hpieceSubset : piece index ⊆ support index := by
      exact Finset.inter_subset_right
    have hcharacterLocal :
        DependsOnlyOn (support index) (character (piece index)) :=
      dependsOnlyOn_mono hpieceSubset (character_dependsOnlyOn (piece index))
    simpa [twisted] using
      (dependsOnlyOn_mul (hlocal index hindex) hcharacterLocal)
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin n → Bool =>
        (∏ index ∈ indices, factor index input) *
          character frequency input) =
      finiteAverage (fun input : Fin n → Bool =>
        ∏ index ∈ indices, twisted index input) := by
          apply finiteAverage_congr
          intro input
          rw [hcharacter input]
          simp only [twisted]
          rw [Finset.prod_mul_distrib]
    _ = ∏ index ∈ indices, finiteAverage (twisted index) :=
      finiteAverage_finset_prod_eq_prod
        indices support twisted htwistedLocal hdisjoint
    _ = ∏ index ∈ indices,
        coefficient (factor index) (frequency ∩ support index) := by
      apply Finset.prod_congr rfl
      intro index _hindex
      rw [coefficient_eq_finiteAverage_mul]

/-- Total coefficient formula.  Frequencies outside the union of the local
supports vanish; frequencies inside it factor into the unique local pieces. -/
theorem coefficient_finset_prod_eq_if_subset
    {n : Nat} {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (support : Index → Finset (Fin n))
    (factor : Index → (Fin n → Bool) → Rat)
    (hlocal : ∀ index ∈ indices,
      DependsOnlyOn (support index) (factor index))
    (hdisjoint : ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right →
      Disjoint (support left) (support right))
    (frequency : Finset (Fin n)) :
    coefficient
        (fun input : Fin n → Bool =>
          ∏ index ∈ indices, factor index input)
        frequency =
      if frequency ⊆ indices.biUnion support then
        ∏ index ∈ indices,
          coefficient (factor index) (frequency ∩ support index)
      else 0 := by
  classical
  by_cases hfrequency : frequency ⊆ indices.biUnion support
  · rw [if_pos hfrequency]
    exact coefficient_finset_prod_eq_prod_inter_of_subset
      indices support factor hlocal hdisjoint frequency hfrequency
  · rw [if_neg hfrequency]
    exact coefficient_eq_zero_of_not_subset_of_dependsOnlyOn
      (dependsOnlyOn_finset_prod indices support factor hlocal) hfrequency

end FiniteBooleanDisjointProductFourierFactorization

end OneTapeMagnification
end Frontier
end Pnp4
