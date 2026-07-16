import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualFixedDifferenceReindex
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# The endpoint sum over nonempty structured-dual coefficients

Fourier inversion and the exact character law of the structured polynomial
generator identify the sum of all Fourier coefficients on its dual code with
the expectation of the function under that generator.  Removing the empty
support subtracts the uniform expectation.  This gives a size-free endpoint
bound for every function taking values in `[0, 1]`.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanOneRoundFoolingBound
open FiniteBooleanMaskedProductFactorization
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualFixedDifferenceReindex

namespace FiniteStructuredDualCoefficientEndpoint

/-- All supports in the exact structured dual code, including the empty
support. -/
def structuredDualSupports
    (n m : Nat) (hn : 0 < n) : Finset (Finset (Fin (2 ^ n))) := by
  classical
  exact Finset.univ.filter (fun support =>
    IsStructuredDualSupport n (structuredIndependence m) hn support)

@[simp]
theorem mem_structuredDualSupports
    (n m : Nat) (hn : 0 < n)
    (support : Finset (Fin (2 ^ n))) :
    support ∈ structuredDualSupports n m hn ↔
      IsStructuredDualSupport n (structuredIndependence m) hn support := by
  classical
  simp [structuredDualSupports]

/-- The signed Fourier endpoint over all nonempty structured-dual supports. -/
def nonemptyStructuredDualCoefficientSum
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat) : Rat :=
  ∑ support ∈ nonemptyStructuredDualSupports n m hn,
    coefficient f support

/-- Averaging Fourier inversion under the structured generator keeps exactly
the coefficients on its dual code. -/
theorem structuredGenerator_finiteAverage_eq_sum_dualCoefficients
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        f ((structuredUnbiasedPrimitive n m hn).generate seed)) =
      ∑ support ∈ structuredDualSupports n m hn,
        coefficient f support := by
  classical
  calc
    finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        f ((structuredUnbiasedPrimitive n m hn).generate seed)) =
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        ∑ support : Finset (Fin (2 ^ n)),
          coefficient f support *
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)) := by
        apply finiteAverage_congr
        intro seed
        exact (fourier_inversion f
          ((structuredUnbiasedPrimitive n m hn).generate seed)).symm
    _ = ∑ support : Finset (Fin (2 ^ n)),
        finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
          coefficient f support *
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)) := by
        exact finiteAverage_fintype_sum _
    _ = ∑ support : Finset (Fin (2 ^ n)),
        coefficient f support *
          finiteAverage (fun seed :
              Fin (structuredIndependence m * n) → Bool =>
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)) := by
        apply Finset.sum_congr rfl
        intro support _
        exact finiteAverage_const_mul _ _
    _ = ∑ support : Finset (Fin (2 ^ n)),
        if IsStructuredDualSupport n (structuredIndependence m) hn support
          then coefficient f support else 0 := by
        apply Finset.sum_congr rfl
        intro support _
        rw [structuredUnbiasedPrimitive_characterAverage_eq_dualIndicator]
        split_ifs <;> ring
    _ = ∑ support ∈ structuredDualSupports n m hn,
        coefficient f support := by
      unfold structuredDualSupports
      rw [Finset.sum_filter]

/-- Removing the empty dual support leaves precisely the existing nonempty
structured-dual support finset. -/
theorem structuredDualSupports_erase_empty
    (n m : Nat) (hn : 0 < n) :
    (structuredDualSupports n m hn).erase ∅ =
      nonemptyStructuredDualSupports n m hn := by
  classical
  ext support
  simp [structuredDualSupports, nonemptyStructuredDualSupports,
    Finset.nonempty_iff_ne_empty]

/-- Exact endpoint identity: the nonempty dual coefficient sum is the
structured-generator expectation minus the uniform expectation. -/
theorem nonemptyStructuredDualCoefficientSum_eq_sub_finiteAverage
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    nonemptyStructuredDualCoefficientSum n m hn f =
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        f ((structuredUnbiasedPrimitive n m hn).generate seed)) -
      finiteAverage f := by
  classical
  have hempty :
      (∅ : Finset (Fin (2 ^ n))) ∈ structuredDualSupports n m hn := by
    simp [isStructuredDualSupport_empty]
  have hsplit := Finset.sum_erase_add (structuredDualSupports n m hn)
    (fun support : Finset (Fin (2 ^ n)) => coefficient f support) hempty
  rw [structuredDualSupports_erase_empty] at hsplit
  unfold nonemptyStructuredDualCoefficientSum
  rw [structuredGenerator_finiteAverage_eq_sum_dualCoefficients n m hn f,
    ← FiniteBooleanMaskedProductFactorization.coefficient_empty_eq_finiteAverage]
  linarith

/-- A pointwise `[0,1]` function has nonempty structured-dual endpoint at
most one, independently of the number of supports. -/
theorem nonemptyStructuredDualCoefficientSum_le_one
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hnonneg : ∀ input, 0 ≤ f input)
    (hle_one : ∀ input, f input ≤ 1) :
    nonemptyStructuredDualCoefficientSum n m hn f ≤ 1 := by
  rw [nonemptyStructuredDualCoefficientSum_eq_sub_finiteAverage]
  have hstructured :
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        f ((structuredUnbiasedPrimitive n m hn).generate seed)) ≤ 1 := by
    have haverage :
        finiteAverage (fun seed :
            Fin (structuredIndependence m * n) → Bool =>
          f ((structuredUnbiasedPrimitive n m hn).generate seed)) ≤
        finiteAverage (fun _ :
            Fin (structuredIndependence m * n) → Bool => (1 : Rat)) := by
      apply DPTWStructuredFullFieldCorrelation.finiteAverage_le_of_pointwise
      intro seed
      exact hle_one _
    simpa using haverage
  have huniform_nonneg : 0 ≤ finiteAverage f := by
    unfold finiteAverage
    exact div_nonneg (Finset.sum_nonneg fun input _ => hnonneg input) (by positivity)
  linarith

end FiniteStructuredDualCoefficientEndpoint
end

end OneTapeMagnification
end Frontier
end Pnp4
