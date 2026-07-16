import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualCount
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyComponentDecomposition

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Signed residual accepted-model pair kernels

A literal residual-model pair count is nonnegative and therefore cannot by
itself expose the cancellation against the low-degree predictor.  This file
keeps that cancellation at the level of individual accepted inputs.

For every accepted model, its atomic deviation is its exact compatible point
mass minus its own low-degree predictor.  The total normalized residual-count
deviation is exactly the sum of these atomic deviations.  Squaring gives an
ordered double sum of signed pair kernels, with no estimate and no additional
assumption.

The final theorem specializes the equality to the mandatory prefixed selector
and rewrites `ResidualModelCountL2Bound` as precisely a budget on the average
signed pair-kernel sum.  No pair-kernel bound is proved here.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanOneRoundFoolingBound
open DPTWStructuredFullFieldCorrelation
open DPTWStructuredFieldCoordinatePrimitive
open FiniteResidualAcceptedModelCount
open MandatoryCanonicalSelectorPairCorrelation

namespace FiniteUnambiguousFBDD

/-! ## Atomic low-degree predictors and signed deviations -/

/-- The low-degree Fourier projection commutes with a sum over a finite type. -/
theorem ratLowDegreeFourierPart_fintype_sum
    {n : Nat} {Index : Type} [Fintype Index]
    (f : Index -> (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (input : Fin n -> Bool) :
    ratLowDegreeFourierPart
        (fun source => ∑ index : Index, f index source) cutoff input =
      ∑ index : Index,
        ratLowDegreeFourierPart (f index) cutoff input := by
  classical
  unfold ratLowDegreeFourierPart
  calc
    (∑ support ∈ lowDegreeSupports n cutoff,
        coefficient (fun source => ∑ index : Index, f index source) support *
          character support input) =
      ∑ support ∈ lowDegreeSupports n cutoff,
        (∑ index : Index, coefficient (f index) support) *
          character support input := by
            apply Finset.sum_congr rfl
            intro support _
            rw [FiniteUnambiguousFBDD.coefficient_fintype_sum f support]
    _ = ∑ support ∈ lowDegreeSupports n cutoff, ∑ index : Index,
        coefficient (f index) support * character support input := by
          apply Finset.sum_congr rfl
          intro support _
          rw [Finset.sum_mul]
    _ = ∑ index : Index, ∑ support ∈ lowDegreeSupports n cutoff,
        coefficient (f index) support * character support input := by
          rw [Finset.sum_comm]

/-- Conditional low-degree predictor contributed by one accepted input. -/
noncomputable def acceptedPointLowDegreePredictor {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    (cutoff : Nat) (base mask : Fin n -> Bool) : Rat :=
  finiteAverage (fun uniform : Fin n -> Bool =>
    ratLowDegreeFourierPart (B.ratAcceptedPointIndicator accepted) cutoff
      (maskedInput base mask uniform))

/-- Exact conditional point mass written directly in compatibility language.
The predictor is intentionally not discarded when this mass is zero. -/
noncomputable def acceptedPointCompatibleMass {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    (base mask : Fin n -> Bool) : Rat := by
  classical
  exact
    if FrozenCompatible accepted.1 base mask then
      1 / (2 : Rat) ^ (liveSupport mask).card
    else 0

/-- Signed atomic residual deviation for one accepted input. -/
noncomputable def acceptedPointResidualDeviation {n : Nat}
    (B : FiniteUnambiguousFBDD n) (accepted : B.AcceptedModel)
    (cutoff : Nat) (base mask : Fin n -> Bool) : Rat :=
  B.acceptedPointCompatibleMass accepted base mask -
    B.acceptedPointLowDegreePredictor accepted cutoff base mask

/-- Ordered signed pair kernel of two accepted inputs. -/
noncomputable def signedResidualAcceptedModelPairKernel {n : Nat}
    (B : FiniteUnambiguousFBDD n) (left right : B.AcceptedModel)
    (cutoff : Nat) (base mask : Fin n -> Bool) : Rat :=
  B.acceptedPointResidualDeviation left cutoff base mask *
    B.acceptedPointResidualDeviation right cutoff base mask

/-- The explicit compatibility mass is the already-defined masked point
mass. -/
theorem acceptedPointCompatibleMass_eq_acceptedPointMaskedMass
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (accepted : B.AcceptedModel) (base mask : Fin n -> Bool) :
    B.acceptedPointCompatibleMass accepted base mask =
      B.acceptedPointMaskedMass accepted base mask := by
  classical
  rw [B.acceptedPointMaskedMass_eq_if_frozenCompatible]
  rfl

/-- Summing exact compatible point masses gives the normalized residual model
count. -/
theorem sum_acceptedPointCompatibleMass_eq_normalizedResidualAcceptedModelCount
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) :
    (∑ accepted : B.AcceptedModel,
        B.acceptedPointCompatibleMass accepted base mask) =
      B.normalizedResidualAcceptedModelCount base mask := by
  classical
  calc
    (∑ accepted : B.AcceptedModel,
        B.acceptedPointCompatibleMass accepted base mask) =
      ∑ accepted : B.AcceptedModel,
        B.acceptedPointMaskedMass accepted base mask := by
          apply Finset.sum_congr rfl
          intro accepted _
          exact B.acceptedPointCompatibleMass_eq_acceptedPointMaskedMass
            accepted base mask
    _ = B.residualAcceptedMass base mask := rfl
    _ = B.normalizedResidualAcceptedModelCount base mask :=
      B.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount base mask

/-- The aggregate low-degree predictor is exactly the sum of the atomic
accepted-point predictors. -/
theorem maskedLowDegreePredictor_ratAcceptanceIndicator_eq_sum_acceptedPoints
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    FiniteBooleanResidualMass.maskedLowDegreePredictor
        B.ratAcceptanceIndicator cutoff base mask =
      ∑ accepted : B.AcceptedModel,
        B.acceptedPointLowDegreePredictor accepted cutoff base mask := by
  classical
  have hindicator :
      B.ratAcceptanceIndicator =
        fun input => ∑ accepted : B.AcceptedModel,
          B.ratAcceptedPointIndicator accepted input := by
    funext input
    exact B.ratAcceptanceIndicator_eq_sum_acceptedPoints input
  unfold FiniteBooleanResidualMass.maskedLowDegreePredictor
    acceptedPointLowDegreePredictor
  rw [hindicator]
  calc
    finiteAverage (fun uniform : Fin n -> Bool =>
        ratLowDegreeFourierPart
          (fun input => ∑ accepted : B.AcceptedModel,
            B.ratAcceptedPointIndicator accepted input)
          cutoff (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin n -> Bool =>
        ∑ accepted : B.AcceptedModel,
          ratLowDegreeFourierPart
            (B.ratAcceptedPointIndicator accepted) cutoff
            (maskedInput base mask uniform)) := by
              apply finiteAverage_congr
              intro uniform
              exact ratLowDegreeFourierPart_fintype_sum
                (fun accepted : B.AcceptedModel =>
                  B.ratAcceptedPointIndicator accepted)
                cutoff (maskedInput base mask uniform)
    _ = ∑ accepted : B.AcceptedModel,
        finiteAverage (fun uniform : Fin n -> Bool =>
          ratLowDegreeFourierPart
            (B.ratAcceptedPointIndicator accepted) cutoff
            (maskedInput base mask uniform)) := by
              rw [finiteAverage_fintype_sum]

/-! ## Exact total and ordered-pair expansions -/

/-- The total normalized residual-count deviation is the exact sum of its
signed accepted-point deviations. -/
theorem normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_eq_sum_pointDeviations
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    B.normalizedResidualAcceptedModelCount base mask -
        FiniteBooleanResidualMass.maskedLowDegreePredictor
          B.ratAcceptanceIndicator cutoff base mask =
      ∑ accepted : B.AcceptedModel,
        B.acceptedPointResidualDeviation accepted cutoff base mask := by
  classical
  rw [← B.sum_acceptedPointCompatibleMass_eq_normalizedResidualAcceptedModelCount
      base mask,
    B.maskedLowDegreePredictor_ratAcceptanceIndicator_eq_sum_acceptedPoints
      cutoff base mask]
  simp only [acceptedPointResidualDeviation, Finset.sum_sub_distrib]

/-- Pointwise, the square of the total residual deviation is the ordered
double sum of the signed accepted-model pair kernels. -/
theorem normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_sq_eq_sum_signedPairKernels
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    (B.normalizedResidualAcceptedModelCount base mask -
        FiniteBooleanResidualMass.maskedLowDegreePredictor
          B.ratAcceptanceIndicator cutoff base mask) ^ 2 =
      ∑ left : B.AcceptedModel, ∑ right : B.AcceptedModel,
        B.signedResidualAcceptedModelPairKernel
          left right cutoff base mask := by
  rw [B.normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_eq_sum_pointDeviations
    cutoff base mask]
  unfold signedResidualAcceptedModelPairKernel
  rw [pow_two, Finset.sum_mul_sum]

/-- Averaging over arbitrary finite base and mask seeds preserves the exact
ordered signed pair-kernel expansion. -/
theorem residualDeviation_secondMoment_eq_sum_signedPairKernelAverages
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (B.normalizedResidualAcceptedModelCount (D seed.1) (T seed.2) -
        FiniteBooleanResidualMass.maskedLowDegreePredictor
          B.ratAcceptanceIndicator cutoff (D seed.1) (T seed.2)) ^ 2) =
      ∑ left : B.AcceptedModel, ∑ right : B.AcceptedModel,
        finiteAverage (fun seed : DSeed × TSeed =>
          B.signedResidualAcceptedModelPairKernel left right cutoff
            (D seed.1) (T seed.2)) := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        (B.normalizedResidualAcceptedModelCount (D seed.1) (T seed.2) -
          FiniteBooleanResidualMass.maskedLowDegreePredictor
            B.ratAcceptanceIndicator cutoff (D seed.1) (T seed.2)) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        ∑ left : B.AcceptedModel, ∑ right : B.AcceptedModel,
          B.signedResidualAcceptedModelPairKernel left right cutoff
            (D seed.1) (T seed.2)) := by
              apply finiteAverage_congr
              intro seed
              exact
                B.normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_sq_eq_sum_signedPairKernels
                  cutoff (D seed.1) (T seed.2)
    _ = ∑ left : B.AcceptedModel, ∑ right : B.AcceptedModel,
        finiteAverage (fun seed : DSeed × TSeed =>
          B.signedResidualAcceptedModelPairKernel left right cutoff
            (D seed.1) (T seed.2)) := by
              rw [finiteAverage_fintype_sum]
              apply Finset.sum_congr rfl
              intro left _
              rw [finiteAverage_fintype_sum]

end FiniteUnambiguousFBDD

namespace MandatoryCanonicalSelectorResidualCount

open FiniteUnambiguousFBDD

/-! ## Mandatory prefixed-selector specialization -/

/-- Exact mandatory-selector second moment as an average sum of the generic
signed accepted-model pair kernels. -/
theorem residualModelCountDeviationSecondMoment_eq_sum_signedPairKernelAverages
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (normalizedResidualCount machine n T b m tailBits hn htail
          rounds seed -
        residualCountLowDegreePredictor machine n T b m tailBits hn htail
          rounds seed) ^ 2) =
      let B := prefixedMandatoryCanonicalSelector machine n T b rounds
      let D := (structuredUnbiasedPrimitive n m hn).generate
      let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
      ∑ left : B.AcceptedModel, ∑ right : B.AcceptedModel,
        finiteAverage (fun seed :
            FiniteBitTape (structuredIndependence m * n) ×
              FiniteBitTape (structuredIndependence m * n) =>
          B.signedResidualAcceptedModelPairKernel left right (2 * m)
            (D seed.1) (mask seed.2)) := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  change
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (B.normalizedResidualAcceptedModelCount (D seed.1) (mask seed.2) -
        FiniteBooleanResidualMass.maskedLowDegreePredictor
          B.ratAcceptanceIndicator (2 * m)
            (D seed.1) (mask seed.2)) ^ 2) =
      ∑ left : B.AcceptedModel, ∑ right : B.AcceptedModel,
        finiteAverage (fun seed :
            FiniteBitTape (structuredIndependence m * n) ×
              FiniteBitTape (structuredIndependence m * n) =>
          B.signedResidualAcceptedModelPairKernel left right (2 * m)
            (D seed.1) (mask seed.2))
  exact B.residualDeviation_secondMoment_eq_sum_signedPairKernelAverages
    (2 * m) D mask

/-- `ResidualModelCountL2Bound` is exactly a budget on the average ordered
sum of the signed accepted-model pair kernels. -/
theorem residualModelCountL2Bound_iff_signedPairKernelBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    ResidualModelCountL2Bound machine n T b m tailBits hn htail rounds <->
      let B := prefixedMandatoryCanonicalSelector machine n T b rounds
      let D := (structuredUnbiasedPrimitive n m hn).generate
      let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
      let p : Rat := 1 / (2 : Rat) ^ tailBits
      (∑ left : B.AcceptedModel, ∑ right : B.AcceptedModel,
        finiteAverage (fun seed :
            FiniteBitTape (structuredIndependence m * n) ×
              FiniteBitTape (structuredIndependence m * n) =>
          B.signedResidualAcceptedModelPairKernel left right (2 * m)
            (D seed.1) (mask seed.2))) <=
        p ^ (2 * m) := by
  unfold ResidualModelCountL2Bound
  dsimp only
  rw [residualModelCountDeviationSecondMoment_eq_sum_signedPairKernelAverages
    machine n T b m tailBits hn htail rounds]

end MandatoryCanonicalSelectorResidualCount

end

end OneTapeMagnification
end Frontier
end Pnp4
