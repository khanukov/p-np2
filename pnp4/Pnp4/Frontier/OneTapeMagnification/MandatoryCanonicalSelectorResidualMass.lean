import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyResidualModelMass
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Residual-mass form of the small-seed selector target

The uniform positive-edge Schur premise is stronger than the signed
selector-pair estimate and can fail because of large Fourier cliques.  This
file states the coefficient-sensitive semantic target instead: after every
generated affine prefix, the residual conditional acceptance mass must be
close in `L2` to its degree-`<= 2m` Fourier predictor.

The target is exactly the structured high-tail second-moment bound.  It gives
the same card-free one-round error and `L * p^m` telescope, while retaining
the coefficient magnitudes and all signed cancellation.  No residual-mass
concentration theorem is asserted here.
-/

noncomputable section

open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanOneRoundFoolingBound
open FiniteBooleanPerVertexRestrictionBound
open DPTWStructuredFieldCoordinatePrimitive
open FiniteAffineRestrictionHybrid
open FiniteUnambiguousFBDD
open MandatoryCanonicalSelectorPairCorrelation

namespace MandatoryCanonicalSelectorResidualMass

/-- Exact semantic `L2` target after one fixed affine prefix. -/
def ResidualMassL2Bound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Prop :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  finiteAverage (fun seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n) =>
    (FiniteBooleanResidualMass.maskedAverage f
        (D seed.1) (mask seed.2) -
      FiniteBooleanResidualMass.maskedLowDegreePredictor f (2 * m)
        (D seed.1) (mask seed.2)) ^ 2) <=
    p ^ (2 * m)

/-- The residual-mass target is literally the structured high-tail
second-moment target, by the exact conditional Fourier identity. -/
theorem structuredSecondMoment_le_pow_of_residualMassL2Bound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hresidual : ResidualMassL2Bound
      machine n T b m tailBits hn htail rounds) :
    let B := prefixedMandatoryCanonicalSelector machine n T b rounds
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        FiniteUnambiguousFBDD.ratHighDegreeFourierTail
          B.ratAcceptanceIndicator (2 * m)
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
            uniform))) ^ 2) <= p ^ (2 * m) := by
  dsimp only
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  have hexact :=
    FiniteBooleanResidualMass.deviation_secondMoment_eq_highTailSecondMoment
      f (2 * m) D mask
  unfold ResidualMassL2Bound at hresidual
  dsimp only at hresidual
  change
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (FiniteBooleanResidualMass.maskedAverage f
          (D seed.1) (mask seed.2) -
        FiniteBooleanResidualMass.maskedLowDegreePredictor f (2 * m)
          (D seed.1) (mask seed.2)) ^ 2) <= p ^ (2 * m) at hresidual
  change
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
          (maskedInput (D seed.1) (mask seed.2) uniform))) ^ 2) <=
      p ^ (2 * m)
  rw [← hexact]
  exact hresidual

/-- The signed dual-far condition is one sufficient way to establish the
semantic residual-mass target. -/
theorem residualMassL2Bound_of_dualFarBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hfar : DualFarBound machine n T b m tailBits hn htail rounds) :
    ResidualMassL2Bound machine n T b m tailBits hn htail rounds := by
  unfold ResidualMassL2Bound
  dsimp only
  rw [FiniteBooleanResidualMass.deviation_secondMoment_eq_highTailSecondMoment]
  exact structuredSecondMoment_le_pow_of_dualFarBound
    machine n T b m tailBits hn htail rounds hfar

/-- Residual-mass `L2` concentration gives the card-free one-round error. -/
theorem oneRoundError_le_pow_of_residualMassL2Bound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hresidual : ResidualMassL2Bound
      machine n T b m tailBits hn htail rounds) :
    let B := prefixedMandatoryCanonicalSelector machine n T b rounds
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          B.ratAcceptanceIndicator
            (maskedInput
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
              uniform))) -
      finiteAverage B.ratAcceptanceIndicator| <= p ^ m := by
  dsimp only
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  have hDlow : IsKWisePatternUnbiased (2 * m) D := by
    apply isKWisePatternUnbiased_of_le (large := structuredIndependence m)
    · unfold structuredIndependence
      omega
    · exact structuredUnbiasedPrimitive_patternUnbiased n m hn
  have hexact := oneRoundAverage_eq_uniformAverage_add_highDegreeAverage
    f D mask hDlow
  have hgap :
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          f (maskedInput (D seed.1) (mask seed.2) uniform))) -
          finiteAverage f =
        finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
          finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
            FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
              (maskedInput (D seed.1) (mask seed.2) uniform))) := by
    rw [hexact]
    ring
  have hsecond := structuredSecondMoment_le_pow_of_residualMassL2Bound
    machine n T b m tailBits hn htail rounds hresidual
  dsimp only at hsecond
  change
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
          (maskedInput (D seed.1) (mask seed.2) uniform))) ^ 2) <=
      p ^ (2 * m) at hsecond
  let tailAverage := fun seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n) =>
    finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
      FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
        (maskedInput (D seed.1) (mask seed.2) uniform))
  have habsSquare :
      (finiteAverage (fun seed => |tailAverage seed|)) ^ 2 <=
        p ^ (2 * m) :=
    (finiteAverage_abs_sq_le_average_sq tailAverage).trans hsecond
  have hp0 : 0 <= p ^ m := by positivity
  have havg0 : 0 <= finiteAverage (fun seed => |tailAverage seed|) :=
    finiteAverage_nonneg fun seed => abs_nonneg _
  have habs : finiteAverage (fun seed => |tailAverage seed|) <= p ^ m := by
    apply FiniteBooleanVertexSumRestrictionBound.le_of_sq_le_sq_of_nonneg
      havg0 hp0
    simpa [show 2 * m = m + m by omega, pow_add, pow_two] using habsSquare
  change
    |finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          f (maskedInput (D seed.1) (mask seed.2) uniform))) -
      finiteAverage f| <= p ^ m
  rw [hgap]
  calc
    |finiteAverage tailAverage| <=
        finiteAverage (fun seed => |tailAverage seed|) :=
      abs_finiteAverage_le_finiteAverage_abs tailAverage
    _ <= p ^ m := habs

/-- Only generated prefixes strictly before round `L` need residual-mass
concentration. -/
def GeneratedPrefixResidualMassL2BoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) : Prop :=
  forall (r : Nat), r < L ->
    forall oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      ResidualMassL2Bound machine n T b m tailBits hn htail
        (roundsOfSeeds
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate
          r oldSeeds)

/-- The generated-prefix residual-mass target yields the exact card-free
multi-round Fourier telescope. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixResidualMassL2BoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hresidual : GeneratedPrefixResidualMassL2BoundUpTo
      machine n T b m tailBits L hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| <= (L : Rat) * p ^ m := by
  dsimp only
  apply FiniteRoundTelescoping.abs_value_sub_initial_le_rounds_mul
  intro round hround
  rw [value_succ_eq_prefixAverage_oneRound]
  unfold value
  rw [← finiteAverage_sub]
  apply abs_finiteAverage_le_of_pointwise_abs_le
  intro oldSeeds
  exact oneRoundError_le_pow_of_residualMassL2Bound
    machine n T b m tailBits hn htail
      (roundsOfSeeds
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate
        round oldSeeds)
      (hresidual round hround oldSeeds)

end MandatoryCanonicalSelectorResidualMass
end

end OneTapeMagnification
end Frontier
end Pnp4
