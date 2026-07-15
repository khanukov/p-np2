import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyFirstDivergenceCharge
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fourier scale of accepted-input point kernels

The exact accepted-input pair expansion isolates the objects to which a
residual-model charge can be applied.  This file records the normalization of
each such atomic object.  A point indicator on an `n`-bit cube has every Walsh
coefficient equal to one sign divided by `2^n`; consequently its total Fourier
energy is `2^-n`, not one.

This closes the diagonal side of the prospective selector-pair estimate at
the correct model-mass scale.  It does not bound off-diagonal accepted-input
correlations; that remains the concrete small-seed selector obligation.
-/

namespace FiniteLayeredQueryProgramFamily

open scoped BigOperators
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanFourierEnergy
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanBoundedIndependenceFarTail

local instance familyIndexFintypeForAcceptedInputFourier {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Fintype family.Index :=
  family.indexFintype

/-- Exact Walsh coefficient of one accepted-input point mass. -/
theorem coefficient_ratAcceptedPointIndicator_eq_character_div
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel) (support : Finset (Fin n)) :
    coefficient (family.ratAcceptedPointIndicator accepted) support =
      character support accepted.1 / (2 : ℚ) ^ n := by
  classical
  unfold coefficient ratAcceptedPointIndicator
  congr 1
  calc
    (∑ input : Fin n → Bool,
        (if input = accepted.1 then 1 else 0) * character support input) =
      (if accepted.1 = accepted.1 then 1 else 0) *
        character support accepted.1 := by
          apply Fintype.sum_eq_single accepted.1
          intro input hinput
          simp [hinput]
    _ = character support accepted.1 := by simp

/-- Every atomic accepted-input coefficient has magnitude exactly `2^-n`. -/
theorem abs_coefficient_ratAcceptedPointIndicator_eq_inv_pow
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel) (support : Finset (Fin n)) :
    |coefficient (family.ratAcceptedPointIndicator accepted) support| =
      1 / (2 : ℚ) ^ n := by
  rw [family.coefficient_ratAcceptedPointIndicator_eq_character_div,
    abs_div, abs_character_eq_one]
  have hpow : 0 ≤ (2 : ℚ) ^ n := by positivity
  rw [abs_of_nonneg hpow]

/-- Parseval energy of one accepted-input point mass is exactly its uniform
mass `2^-n`. -/
theorem sum_sq_coefficient_ratAcceptedPointIndicator_eq_inv_pow
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel) :
    (∑ support : Finset (Fin n),
      (coefficient (family.ratAcceptedPointIndicator accepted) support) ^ 2) =
      1 / (2 : ℚ) ^ n := by
  rw [parseval]
  unfold finiteAverage ratAcceptedPointIndicator
  have hsum :
      (∑ input : Fin n → Bool,
        (if input = accepted.1 then (1 : ℚ) else 0) ^ 2) = 1 := by
    classical
    calc
      (∑ input : Fin n → Bool,
          (if input = accepted.1 then (1 : ℚ) else 0) ^ 2) =
        (if accepted.1 = accepted.1 then (1 : ℚ) else 0) ^ 2 := by
          apply Fintype.sum_eq_single accepted.1
          intro input hinput
          simp [hinput]
      _ = 1 := by simp
  rw [hsum]
  simp

/-- The diagonal high-tail contribution of one accepted input carries the
correct atomic `2^-n` normalization. -/
theorem acceptedPoint_highTail_diagonalEnergy_le_invPow_mul_pow_succ
    {n cutoff q : Nat} {TSeed : Type*}
    [Fintype TSeed] [Nonempty TSeed]
    (family : FiniteLayeredQueryProgramFamily n)
    (accepted : family.AcceptedModel)
    (T : TSeed → Fin n → Bool) (p : ℚ) (hp0 : 0 ≤ p)
    (hcutoffQ : cutoff + 1 ≤ q)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased q p T) :
    (∑ support ∈ highDegreeSupports n cutoff,
      (coefficient (family.ratAcceptedPointIndicator accepted) support) ^ 2 *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator support (T t))) ≤
      (1 / (2 : ℚ) ^ n) * p ^ (cutoff + 1) := by
  calc
    (∑ support ∈ highDegreeSupports n cutoff,
        (coefficient (family.ratAcceptedPointIndicator accepted) support) ^ 2 *
          finiteAverage (fun t : TSeed =>
            maskAllZeroIndicator support (T t))) ≤
      ∑ support ∈ highDegreeSupports n cutoff,
        (coefficient (family.ratAcceptedPointIndicator accepted) support) ^ 2 *
          p ^ (cutoff + 1) := by
            apply Finset.sum_le_sum
            intro support hsupport
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            exact maskAllZeroIndicator_average_le_pow_of_cardLowerBound
              T p hT support hcutoffQ
                (by
                  have := mem_highDegreeSupports.mp hsupport
                  omega)
    _ = p ^ (cutoff + 1) *
        ∑ support ∈ highDegreeSupports n cutoff,
          (coefficient
            (family.ratAcceptedPointIndicator accepted) support) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro support _
      ring
    _ ≤ p ^ (cutoff + 1) *
        ∑ support : Finset (Fin n),
          (coefficient
            (family.ratAcceptedPointIndicator accepted) support) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp0 _)
      exact Finset.sum_le_univ_sum_of_nonneg fun support =>
        sq_nonneg (coefficient
          (family.ratAcceptedPointIndicator accepted) support)
    _ = p ^ (cutoff + 1) * (1 / (2 : ℚ) ^ n) := by
      rw [family.sum_sq_coefficient_ratAcceptedPointIndicator_eq_inv_pow]
    _ = (1 / (2 : ℚ) ^ n) * p ^ (cutoff + 1) := by ring

/-- Summing the atomic diagonal terms over every accepted input is still
size-free: accepted inputs form a subtype of the Boolean cube, so their total
uniform mass is at most one. -/
theorem sum_acceptedPoint_highTail_diagonalEnergy_le_pow_succ
    {n cutoff q : Nat} {TSeed : Type*}
    [Fintype TSeed] [Nonempty TSeed]
    (family : FiniteLayeredQueryProgramFamily n)
    (T : TSeed → Fin n → Bool) (p : ℚ) (hp0 : 0 ≤ p)
    (hcutoffQ : cutoff + 1 ≤ q)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased q p T) :
    (∑ accepted : family.AcceptedModel,
      ∑ support ∈ highDegreeSupports n cutoff,
        (coefficient (family.ratAcceptedPointIndicator accepted) support) ^ 2 *
          finiteAverage (fun t : TSeed =>
            maskAllZeroIndicator support (T t))) ≤
      p ^ (cutoff + 1) := by
  have hcardNat : Fintype.card family.AcceptedModel ≤ 2 ^ n := by
    calc
      Fintype.card family.AcceptedModel ≤
          Fintype.card (Fin n → Bool) :=
        Fintype.card_subtype_le _
      _ = 2 ^ n := by simp
  have hratio :
      (Fintype.card family.AcceptedModel : ℚ) / (2 : ℚ) ^ n ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℚ) < (2 : ℚ) ^ n)).2
    exact_mod_cast hcardNat
  calc
    (∑ accepted : family.AcceptedModel,
        ∑ support ∈ highDegreeSupports n cutoff,
          (coefficient
            (family.ratAcceptedPointIndicator accepted) support) ^ 2 *
            finiteAverage (fun t : TSeed =>
              maskAllZeroIndicator support (T t))) ≤
      ∑ _accepted : family.AcceptedModel,
        (1 / (2 : ℚ) ^ n) * p ^ (cutoff + 1) := by
          apply Finset.sum_le_sum
          intro accepted _
          exact family.acceptedPoint_highTail_diagonalEnergy_le_invPow_mul_pow_succ
            accepted T p hp0 hcutoffQ hT
    _ = ((Fintype.card family.AcceptedModel : ℚ) / (2 : ℚ) ^ n) *
        p ^ (cutoff + 1) := by
          simp
          ring
    _ ≤ 1 * p ^ (cutoff + 1) := by
      apply mul_le_mul_of_nonneg_right hratio
      exact pow_nonneg hp0 _
    _ = p ^ (cutoff + 1) := one_mul _

end FiniteLayeredQueryProgramFamily
end OneTapeMagnification
end Frontier
end Pnp4
