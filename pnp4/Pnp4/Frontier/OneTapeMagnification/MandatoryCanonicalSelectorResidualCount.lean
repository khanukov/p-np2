import Pnp4.Frontier.OneTapeMagnification.FiniteResidualAcceptedModelCount
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorResidualMass

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Literal residual-count form of the mandatory selector target

`ResidualMassL2Bound` is the exact high-tail target, but a path-splicing
argument acts on residual models and ordered pairs of residual models.  This
file rewrites the target into that literal finite-count language.

For each structured base/mask seed, the residual mass is exactly

`compatible accepted models / 2^|live coordinates|`.

Its square is the compatible ordered-pair count divided by
`2^(2 * |live coordinates|)`.  The low-degree predictor and its cross term
are retained exactly; dropping either would lose the signed cancellation
required by the small-seed selector-pair lemma.

No count concentration, last-common-prefix telescope, or splice injection is
asserted here.
-/

noncomputable section

open FiniteBooleanRestrictionMoment
open DPTWStructuredFieldCoordinatePrimitive
open FiniteAffineRestrictionHybrid
open FiniteResidualAcceptedModelCount
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorResidualMass

namespace MandatoryCanonicalSelectorResidualCount

/-- Exact normalized compatible-model count after one fixed affine prefix. -/
noncomputable def normalizedResidualCount
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) : Rat :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  B.normalizedResidualAcceptedModelCount (D seed.1) (mask seed.2)

/-- Exact normalized compatible ordered-pair count after one affine prefix. -/
noncomputable def normalizedResidualPairCount
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) : Rat :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  (B.residualAcceptedModelPairCount (D seed.1) (mask seed.2) : Rat) /
    (2 : Rat) ^
      (2 * (liveSupport (mask seed.2)).card)

/-- Low-degree predictor paired with the literal residual count. -/
noncomputable def residualCountLowDegreePredictor
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) : Rat :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  FiniteBooleanResidualMass.maskedLowDegreePredictor
    B.ratAcceptanceIndicator (2 * m) (D seed.1) (mask seed.2)

/-- The small-seed selector lemma in literal compatible-model-count form. -/
def ResidualModelCountL2Bound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Prop :=
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  finiteAverage (fun seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n) =>
    (normalizedResidualCount machine n T b m tailBits hn htail
        rounds seed -
      residualCountLowDegreePredictor machine n T b m tailBits hn htail
        rounds seed) ^ 2) <=
    p ^ (2 * m)

/-- Pointwise square expansion into the normalized ordered-pair count and the
exact predictor cross term. -/
theorem residualCount_deviation_sq_eq_pairCount_sub_cross
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) :
    (normalizedResidualCount machine n T b m tailBits hn htail rounds seed -
      residualCountLowDegreePredictor machine n T b m tailBits hn htail
        rounds seed) ^ 2 =
      normalizedResidualPairCount machine n T b m tailBits hn htail
          rounds seed -
        2 * normalizedResidualCount machine n T b m tailBits hn htail
            rounds seed *
          residualCountLowDegreePredictor machine n T b m tailBits hn htail
            rounds seed +
        (residualCountLowDegreePredictor machine n T b m tailBits hn htail
          rounds seed) ^ 2 := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  change
    (B.normalizedResidualAcceptedModelCount (D seed.1) (mask seed.2) -
      FiniteBooleanResidualMass.maskedLowDegreePredictor
        B.ratAcceptanceIndicator (2 * m)
          (D seed.1) (mask seed.2)) ^ 2 =
      (B.residualAcceptedModelPairCount
          (D seed.1) (mask seed.2) : Rat) /
          (2 : Rat) ^ (2 * (liveSupport (mask seed.2)).card) -
        2 * B.normalizedResidualAcceptedModelCount
            (D seed.1) (mask seed.2) *
          FiniteBooleanResidualMass.maskedLowDegreePredictor
            B.ratAcceptanceIndicator (2 * m)
              (D seed.1) (mask seed.2) +
        (FiniteBooleanResidualMass.maskedLowDegreePredictor
          B.ratAcceptanceIndicator (2 * m)
            (D seed.1) (mask seed.2)) ^ 2
  exact B.normalizedResidualAcceptedModelCount_sub_sq_eq_pairCount_sub_cross
    (D seed.1) (mask seed.2)
      (FiniteBooleanResidualMass.maskedLowDegreePredictor
        B.ratAcceptanceIndicator (2 * m) (D seed.1) (mask seed.2))

/-- `ResidualModelCountL2Bound` is exactly the residual-mass target, not a
relaxation of it. -/
theorem residualModelCountL2Bound_iff_residualMassL2Bound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    ResidualModelCountL2Bound machine n T b m tailBits hn htail rounds <->
      ResidualMassL2Bound machine n T b m tailBits hn htail rounds := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  unfold ResidualModelCountL2Bound ResidualMassL2Bound
  dsimp only
  apply iff_of_eq
  congr 1
  apply finiteAverage_congr
  intro seed
  change
    (B.normalizedResidualAcceptedModelCount (D seed.1) (mask seed.2) -
      FiniteBooleanResidualMass.maskedLowDegreePredictor
        B.ratAcceptanceIndicator (2 * m) (D seed.1) (mask seed.2)) ^ 2 =
    (FiniteBooleanResidualMass.maskedAverage B.ratAcceptanceIndicator
        (D seed.1) (mask seed.2) -
      FiniteBooleanResidualMass.maskedLowDegreePredictor
        B.ratAcceptanceIndicator (2 * m) (D seed.1) (mask seed.2)) ^ 2
  rw [FiniteUnambiguousFBDD.maskedAverage_ratAcceptanceIndicator_eq_residualAcceptedMass,
    B.residualAcceptedMass_eq_normalizedResidualAcceptedModelCount]

/-- Equivalent average inequality written directly with literal compatible
ordered-pair counts and the signed predictor correction. -/
theorem residualModelCountL2Bound_iff_pairCountCrossBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    ResidualModelCountL2Bound machine n T b m tailBits hn htail rounds <->
      let p : Rat := 1 / (2 : Rat) ^ tailBits
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        normalizedResidualPairCount machine n T b m tailBits hn htail
              rounds seed -
          2 * normalizedResidualCount machine n T b m tailBits hn htail
                rounds seed *
            residualCountLowDegreePredictor machine n T b m tailBits hn htail
              rounds seed +
          (residualCountLowDegreePredictor machine n T b m tailBits hn htail
            rounds seed) ^ 2) <=
        p ^ (2 * m) := by
  dsimp only
  unfold ResidualModelCountL2Bound
  dsimp only
  apply iff_of_eq
  congr 1
  apply finiteAverage_congr
  intro seed
  exact residualCount_deviation_sq_eq_pairCount_sub_cross
    machine n T b m tailBits hn htail rounds seed

/-- Literal residual-count concentration gives the card-free one-round
error through the exact residual-mass equivalence. -/
theorem oneRoundError_le_pow_of_residualModelCountL2Bound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hcount : ResidualModelCountL2Bound
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
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              uniform))) -
      finiteAverage B.ratAcceptanceIndicator| <= p ^ m := by
  exact oneRoundError_le_pow_of_residualMassL2Bound
    machine n T b m tailBits hn htail rounds
      ((residualModelCountL2Bound_iff_residualMassL2Bound
        machine n T b m tailBits hn htail rounds).1 hcount)

/-- Only generated prefixes before round `L` need the literal residual-count
bound. -/
def GeneratedPrefixResidualModelCountL2BoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) : Prop :=
  forall (r : Nat), r < L ->
    forall oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      ResidualModelCountL2Bound machine n T b m tailBits hn htail
        (roundsOfSeeds
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate
          r oldSeeds)

/-- The generated-prefix literal count bound is exactly the previously stated
generated-prefix residual-mass bound. -/
theorem generatedPrefixResidualModelCountL2BoundUpTo_iff_residualMass
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) :
    GeneratedPrefixResidualModelCountL2BoundUpTo
        machine n T b m tailBits L hn htail <->
      GeneratedPrefixResidualMassL2BoundUpTo
        machine n T b m tailBits L hn htail := by
  constructor
  · intro hcount r hr oldSeeds
    exact (residualModelCountL2Bound_iff_residualMassL2Bound
      machine n T b m tailBits hn htail _).1 (hcount r hr oldSeeds)
  · intro hmass r hr oldSeeds
    exact (residualModelCountL2Bound_iff_residualMassL2Bound
      machine n T b m tailBits hn htail _).2 (hmass r hr oldSeeds)

/-- The exact generated-prefix count target yields the card-free multi-round
Fourier telescope. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixResidualModelCountL2BoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hcount : GeneratedPrefixResidualModelCountL2BoundUpTo
      machine n T b m tailBits L hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| <= (L : Rat) * p ^ m := by
  exact
    abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixResidualMassL2BoundUpTo
      machine n T b m tailBits L hn htail
        ((generatedPrefixResidualModelCountL2BoundUpTo_iff_residualMass
          machine n T b m tailBits L hn htail).1 hcount)

end MandatoryCanonicalSelectorResidualCount
end

end OneTapeMagnification
end Frontier
end Pnp4
