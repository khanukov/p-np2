import Pnp4.Frontier.OneTapeMagnification.FiniteWeightedChargeSpectral
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Coefficient-sensitive positive-edge charge for selector prefixes

Uniform row-charge weights test the spectral radius of the positive Fourier
graph and are stronger than the single coefficient-vector estimate needed by
the hybrid.  This module keeps the actual Fourier energy on every row.

With the canonical weights `|fhat(S)|`, the positive-edge quadratic form is
exactly `sum_S beta(S) * fhat(S)^2`, where `beta(S)` is the realized local
charge `(K |fhat|)_S / |fhat(S)|`.  Bounding this energy-weighted sum at every
generated affine prefix implies the original signed `DualFarBound` and hence
the card-free telescope.  Negative Fourier edges are still discarded, so the
new premise remains sufficient rather than equivalent to the signed target.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanFullIndependenceRestriction
open FiniteAffineRestrictionHybrid
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredRankWeightedDualCorrelation
open DPTWStructuredWeightedCharge
open FiniteWeightedChargeSpectral
open MandatoryCanonicalSelectorPairCorrelation

namespace MandatoryCanonicalSelectorEnergyCharge

/-- The exact coefficient-sensitive positive-edge budget after one affine
prefix.  Large local graph charge is allowed on supports carrying little
Fourier energy. -/
def SelectorPositiveEdgeEnergyBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Prop :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  (∑ support ∈ activeHighDegreeSupports (2 * m) f,
      structuredPositivePairLocalBudget
          n m tailBits (2 * m) hn htail f support *
        (coefficient f support) ^ 2) <=
    (1 - p) * p ^ (2 * m)

/-- The coefficient-sensitive energy charge implies the exact signed
selector-pair premise. -/
theorem dualFarBound_of_selectorPositiveEdgeEnergyBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (henergy : SelectorPositiveEdgeEnergyBound
      machine n T b m tailBits hn htail rounds) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  have henergy' := henergy
  change
    (∑ support ∈ activeHighDegreeSupports (2 * m) f,
        structuredPositivePairLocalBudget
            n m tailBits (2 * m) hn htail f support *
          (coefficient f support) ^ 2) <=
      (1 - p) * p ^ (2 * m) at henergy'
  have hfar :
      structuredDualFarPairCorrelation n m tailBits (2 * m) hn htail f <=
        (1 - p) * p ^ (2 * m) := by
    rw [structuredDualFarPairCorrelation_eq_rankWeighted]
    calc
      structuredRankWeightedDualFarPairCorrelation
          n m tailBits (2 * m) hn htail f <=
        signedQuadraticSum (activeHighDegreeSupports (2 * m) f)
          (coefficient f)
          (structuredPositivePairKernel n m tailBits hn htail f) :=
        structuredRankWeightedDualFarPairCorrelation_le_positivePairSum
          n m tailBits (2 * m) hn htail f
      _ = ∑ support ∈ activeHighDegreeSupports (2 * m) f,
          structuredPositivePairLocalBudget
              n m tailBits (2 * m) hn htail f support *
            (coefficient f support) ^ 2 :=
        signedQuadraticSum_positivePair_eq_localBudgetEnergy
          n m tailBits (2 * m) hn htail f
      _ <= (1 - p) * p ^ (2 * m) := henergy'
  simpa [DualFarBound, B, f, p] using hfar

/-- For an `L`-round hybrid, require the energy-weighted positive-edge budget
only for the generated prefixes at depths `r < L`. -/
def GeneratedPrefixSelectorPositiveEdgeEnergyBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) : Prop :=
  forall (r : Nat), r < L ->
    forall oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      SelectorPositiveEdgeEnergyBound machine n T b m tailBits hn htail
        (roundsOfSeeds
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate
          r oldSeeds)

/-- Generated-prefix energy charge discharges the existing generated-prefix
signed correlation obligation. -/
theorem generatedPrefixDualFarBoundUpTo_of_selectorPositiveEdgeEnergyBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (henergy : GeneratedPrefixSelectorPositiveEdgeEnergyBoundUpTo
      machine n T b m tailBits L hn htail) :
    GeneratedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail := by
  intro r hr oldSeeds
  exact dualFarBound_of_selectorPositiveEdgeEnergyBound
    machine n T b m tailBits hn htail _ (henergy r hr oldSeeds)

/-- The coefficient-sensitive generated-prefix charge is sufficient for the
card-free `L * p^m` Fourier hybrid error. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixSelectorPositiveEdgeEnergyBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (henergy : GeneratedPrefixSelectorPositiveEdgeEnergyBoundUpTo
      machine n T b m tailBits L hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| <= (L : Rat) * p ^ m := by
  exact
    abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail
        (generatedPrefixDualFarBoundUpTo_of_selectorPositiveEdgeEnergyBoundUpTo
          machine n T b m tailBits L hn htail henergy)

end MandatoryCanonicalSelectorEnergyCharge
end

end OneTapeMagnification
end Frontier
end Pnp4
