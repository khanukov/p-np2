import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualSyndromeFiberBlocks
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanDisjointProductFourierFactorization
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact syndrome transform of a disjoint block product

For one fixed mask, the sum of the high Fourier coefficients in each
structured power-syndrome fiber has an exact finite Fourier transform over
the structured seed space.  If the underlying function is a product of
functions on pairwise-disjoint coordinate blocks, its full transform factors
block by block.  The strict high-degree transform is therefore that product
minus the explicitly displayed low-degree polynomial.

This file proves identities only.  It does not assume or claim the
quantitative leakage estimate needed at the selector-correlation frontier.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanMaskedProductFactorization
open FiniteBooleanDisjointProductFourierFactorization
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open FiniteStructuredDualSyndromeFiberBlocks
open FiniteStructuredDualNonzeroSeedCorrelation

namespace FiniteStructuredDualBlockProductSyndromeTransform

/-- The fixed-mask structured transform restricted to Fourier degrees
strictly above `cutoff`. -/
def structuredMaskedHighDegreeTransform
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) : Rat :=
  ∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
    structuredMaskedCoefficient f mask support *
      character support ((structuredUnbiasedPrimitive n m hn).generate seed)

/-- The complementary low-degree polynomial, with the cutoff visible in
the definition rather than hidden in a residual hypothesis. -/
def structuredMaskedLowDegreePolynomial
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) : Rat :=
  ∑ support : Finset (Fin (2 ^ n)),
    if support.card <= cutoff then
      structuredMaskedCoefficient f mask support *
        character support ((structuredUnbiasedPrimitive n m hn).generate seed)
    else 0

/-- The high transform is the full fixed-mask conditional expectation minus
the explicitly retained low-degree polynomial. -/
theorem structuredMaskedHighDegreeTransform_eq_fixedMask_sub_low
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    structuredMaskedHighDegreeTransform n m cutoff hn f mask seed =
      fixedMaskAveragedFunction f mask
          ((structuredUnbiasedPrimitive n m hn).generate seed) -
        structuredMaskedLowDegreePolynomial n m cutoff hn f mask seed := by
  classical
  rw [fixedMaskAveragedFunction_eq_frozenFourierSum]
  unfold structuredMaskedHighDegreeTransform
    structuredMaskedLowDegreePolynomial structuredMaskedCoefficient
    highDegreeSupports
  rw [Finset.sum_filter]
  apply Eq.symm
  rw [sub_eq_iff_eq_add]
  calc
    (∑ support : Finset (Fin (2 ^ n)),
        coefficient f support *
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed) *
          maskAllZeroIndicator support mask) =
      ∑ support : Finset (Fin (2 ^ n)),
        ((if support.card <= cutoff then
            (maskAllZeroIndicator support mask * coefficient f support) *
              character support
                ((structuredUnbiasedPrimitive n m hn).generate seed)
          else 0) +
        if cutoff < support.card then
          (maskAllZeroIndicator support mask * coefficient f support) *
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)
        else 0) := by
          apply Finset.sum_congr rfl
          intro support _hsupport
          by_cases hlow : support.card <= cutoff
          · have hnotHigh : ¬ cutoff < support.card := by omega
            simp [hlow, hnotHigh]
            ring
          · have hhigh : cutoff < support.card := by omega
            simp [hlow, hhigh]
            ring
    _ =
      (∑ support : Finset (Fin (2 ^ n)),
        if support.card <= cutoff then
          (maskAllZeroIndicator support mask * coefficient f support) *
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)
        else 0) +
      ∑ support : Finset (Fin (2 ^ n)),
        if cutoff < support.card then
          (maskAllZeroIndicator support mask * coefficient f support) *
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)
        else 0 := by
          rw [Finset.sum_add_distrib]
    _ =
      (∑ support : Finset (Fin (2 ^ n)),
        if cutoff < support.card then
          (maskAllZeroIndicator support mask * coefficient f support) *
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)
        else 0) +
      ∑ support : Finset (Fin (2 ^ n)),
        if support.card <= cutoff then
          (maskAllZeroIndicator support mask * coefficient f support) *
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)
        else 0 := by
          rw [add_comm]

/-- Exact product form of the high structured transform.  The only
non-product term is the displayed global low-degree polynomial. -/
theorem structuredMaskedHighDegreeTransform_disjointProduct_eq_prod_sub_low
    (n m cutoff : Nat) (hn : 0 < n)
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index)
    (support : Index -> Finset (Fin (2 ^ n)))
    (factor : Index -> (Fin (2 ^ n) -> Bool) -> Rat)
    (hlocal : ∀ index ∈ indices,
      DependsOnlyOn (support index) (factor index))
    (hdisjoint : ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right ->
      Disjoint (support left) (support right))
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    structuredMaskedHighDegreeTransform n m cutoff hn
        (fun input => ∏ index ∈ indices, factor index input) mask seed =
      (∏ index ∈ indices,
        fixedMaskAveragedFunction (factor index) mask
          ((structuredUnbiasedPrimitive n m hn).generate seed)) -
        structuredMaskedLowDegreePolynomial n m cutoff hn
          (fun input => ∏ index ∈ indices, factor index input) mask seed := by
  rw [structuredMaskedHighDegreeTransform_eq_fixedMask_sub_low]
  congr 1
  exact finiteAverage_finset_prod_maskedInput_eq_prod
    indices support factor hlocal hdisjoint
      ((structuredUnbiasedPrimitive n m hn).generate seed) mask

private theorem fiberBlockSum_eq_equalLabelPairs
    {Index Label : Type*} [Fintype Label]
    [DecidableEq Index] [DecidableEq Label]
    (indices : Finset Index) (label : Index -> Label)
    (leftTerm rightTerm : Index -> Rat) :
    (∑ fiber : Label,
        (∑ left ∈ indices,
          if label left = fiber then leftTerm left else 0) *
        (∑ right ∈ indices,
          if label right = fiber then rightTerm right else 0)) =
      ∑ left ∈ indices, ∑ right ∈ indices,
        if label left = label right then
          leftTerm left * rightTerm right
        else 0 := by
  classical
  calc
    (∑ fiber : Label,
        (∑ left ∈ indices,
          if label left = fiber then leftTerm left else 0) *
        (∑ right ∈ indices,
          if label right = fiber then rightTerm right else 0)) =
      ∑ fiber : Label, ∑ left ∈ indices, ∑ right ∈ indices,
        (if label left = fiber then leftTerm left else 0) *
          (if label right = fiber then rightTerm right else 0) := by
            apply Fintype.sum_congr
            intro fiber
            rw [Finset.sum_mul_sum]
    _ = ∑ left ∈ indices, ∑ right ∈ indices, ∑ fiber : Label,
        (if label left = fiber then leftTerm left else 0) *
          (if label right = fiber then rightTerm right else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro left _hleft
            rw [Finset.sum_comm]
    _ = ∑ left ∈ indices, ∑ right ∈ indices,
        if label left = label right then
          leftTerm left * rightTerm right
        else 0 := by
          apply Finset.sum_congr rfl
          intro left _hleft
          apply Finset.sum_congr rfl
          intro right _hright
          by_cases heq : label left = label right
          · rw [heq]
            simp
          · rw [if_neg heq]
            apply Fintype.sum_eq_zero
            intro fiber
            by_cases hleft : label left = fiber
            · have hright : label right ≠ fiber := by
                intro hright
                exact heq (hleft.trans hright.symm)
              simp [hleft, hright]
            · simp [hleft]

/-- Parseval on the finite structured seed space, stated directly in the
power-syndrome basis.  This is the exact bridge between the syndrome-fiber
energy and the structured transform; there is no inequality or missing
normalization factor. -/
theorem syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
    (n m cutoff : Nat) (hn : 0 < n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    (∑ syndrome : StructuredDualPowerSyndrome n m,
      structuredSyndromeFiberCoefficientSum n m cutoff hn
          leftFunction mask syndrome *
        structuredSyndromeFiberCoefficientSum n m cutoff hn
          rightFunction mask syndrome) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          structuredMaskedHighDegreeTransform n m cutoff hn
              leftFunction mask seed *
            structuredMaskedHighDegreeTransform n m cutoff hn
              rightFunction mask seed) := by
  classical
  let high := highDegreeSupports (2 ^ n) cutoff
  let leftTerm := structuredMaskedCoefficient leftFunction mask
  let rightTerm := structuredMaskedCoefficient rightFunction mask
  let base := fun seed : Fin (structuredIndependence m * n) -> Bool =>
    (structuredUnbiasedPrimitive n m hn).generate seed
  have hfibers :
      (∑ syndrome : StructuredDualPowerSyndrome n m,
        structuredSyndromeFiberCoefficientSum n m cutoff hn
            leftFunction mask syndrome *
          structuredSyndromeFiberCoefficientSum n m cutoff hn
            rightFunction mask syndrome) =
        ∑ left ∈ high, ∑ right ∈ high,
          if structuredDualPowerSyndrome n m hn left =
              structuredDualPowerSyndrome n m hn right then
            leftTerm left * rightTerm right
          else 0 := by
    simpa [structuredSyndromeFiberCoefficientSum, high, leftTerm,
      rightTerm] using
      (fiberBlockSum_eq_equalLabelPairs
        (indices := high)
        (label := structuredDualPowerSyndrome n m hn)
        (leftTerm := leftTerm) (rightTerm := rightTerm))
  rw [hfibers]
  unfold structuredMaskedHighDegreeTransform
  change
    (∑ left ∈ high, ∑ right ∈ high,
      if structuredDualPowerSyndrome n m hn left =
          structuredDualPowerSyndrome n m hn right then
        leftTerm left * rightTerm right
      else 0) =
    finiteAverage (fun seed =>
      (∑ left ∈ high,
        leftTerm left * character left (base seed)) *
      ∑ right ∈ high,
        rightTerm right * character right (base seed))
  calc
    (∑ left ∈ high, ∑ right ∈ high,
        if structuredDualPowerSyndrome n m hn left =
            structuredDualPowerSyndrome n m hn right then
          leftTerm left * rightTerm right
        else 0) =
      ∑ left ∈ high, ∑ right ∈ high,
        (leftTerm left * rightTerm right) *
          finiteAverage (fun seed :
              Fin (structuredIndependence m * n) -> Bool =>
            character left (base seed) * character right (base seed)) := by
              apply Finset.sum_congr rfl
              intro left _hleft
              apply Finset.sum_congr rfl
              intro right _hright
              rw [structuredUnbiasedPrimitive_characterPairAverage_eq_dualIndicator]
              have hiff :=
                isStructuredDualSupport_symmDiff_iff_syndrome_eq
                  n m hn left right
              by_cases heq : structuredDualPowerSyndrome n m hn left =
                  structuredDualPowerSyndrome n m hn right
              · have hdual : IsStructuredDualSupport n
                    (structuredIndependence m) hn (left ∆ right) :=
                  hiff.mpr heq
                simp [heq, hdual]
              · have hnotDual : ¬ IsStructuredDualSupport n
                    (structuredIndependence m) hn (left ∆ right) := by
                  intro hdual
                  exact heq (hiff.mp hdual)
                simp [heq, hnotDual]
    _ = finiteAverage (fun seed =>
        ∑ left ∈ high, ∑ right ∈ high,
          (leftTerm left * rightTerm right) *
            (character left (base seed) * character right (base seed))) := by
              rw [finiteAverage_finset_sum]
              apply Finset.sum_congr rfl
              intro left _hleft
              rw [finiteAverage_finset_sum]
              apply Finset.sum_congr rfl
              intro right _hright
              rw [finiteAverage_const_mul]
    _ = finiteAverage (fun seed =>
        (∑ left ∈ high,
          leftTerm left * character left (base seed)) *
        ∑ right ∈ high,
          rightTerm right * character right (base seed)) := by
            apply finiteAverage_congr
            intro seed
            rw [Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro left _hleft
            apply Finset.sum_congr rfl
            intro right _hright
            ring

/-- Squared syndrome energy of one function, in the exact product-minus-low
normal form used by the fixed-alpha leakage problem. -/
theorem syndromeFiberEnergy_disjointProduct_eq_average_prod_sub_low_sq
    (n m cutoff : Nat) (hn : 0 < n)
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index)
    (support : Index -> Finset (Fin (2 ^ n)))
    (factor : Index -> (Fin (2 ^ n) -> Bool) -> Rat)
    (hlocal : ∀ index ∈ indices,
      DependsOnlyOn (support index) (factor index))
    (hdisjoint : ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right ->
      Disjoint (support left) (support right))
    (mask : Fin (2 ^ n) -> Bool) :
    let productFunction := fun input =>
      ∏ index ∈ indices, factor index input
    (∑ syndrome : StructuredDualPowerSyndrome n m,
      (structuredSyndromeFiberCoefficientSum n m cutoff hn
        productFunction mask syndrome) ^ 2) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          ((∏ index ∈ indices,
              fixedMaskAveragedFunction (factor index) mask
                ((structuredUnbiasedPrimitive n m hn).generate seed)) -
            structuredMaskedLowDegreePolynomial n m cutoff hn
              productFunction mask seed) ^ 2) := by
  dsimp only
  calc
    (∑ syndrome : StructuredDualPowerSyndrome n m,
        (structuredSyndromeFiberCoefficientSum n m cutoff hn
          (fun input => ∏ index ∈ indices, factor index input)
          mask syndrome) ^ 2) =
      ∑ syndrome : StructuredDualPowerSyndrome n m,
        structuredSyndromeFiberCoefficientSum n m cutoff hn
            (fun input => ∏ index ∈ indices, factor index input)
            mask syndrome *
          structuredSyndromeFiberCoefficientSum n m cutoff hn
            (fun input => ∏ index ∈ indices, factor index input)
            mask syndrome := by
              apply Finset.sum_congr rfl
              intro syndrome _hsyndrome
              rw [pow_two]
    _ = finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          structuredMaskedHighDegreeTransform n m cutoff hn
              (fun input => ∏ index ∈ indices, factor index input) mask seed *
            structuredMaskedHighDegreeTransform n m cutoff hn
              (fun input => ∏ index ∈ indices, factor index input) mask seed) :=
      syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
        n m cutoff hn _ _ mask
    _ = finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          ((∏ index ∈ indices,
              fixedMaskAveragedFunction (factor index) mask
                ((structuredUnbiasedPrimitive n m hn).generate seed)) -
            structuredMaskedLowDegreePolynomial n m cutoff hn
              (fun input => ∏ index ∈ indices, factor index input)
              mask seed) ^ 2) := by
                apply finiteAverage_congr
                intro seed
                rw [structuredMaskedHighDegreeTransform_disjointProduct_eq_prod_sub_low
                  n m cutoff hn indices support factor hlocal hdisjoint mask seed]
                ring

end FiniteStructuredDualBlockProductSyndromeTransform
end
end OneTapeMagnification
end Frontier
end Pnp4
