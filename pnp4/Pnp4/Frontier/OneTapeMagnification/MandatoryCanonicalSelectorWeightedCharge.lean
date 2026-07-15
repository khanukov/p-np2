import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Weighted-charge criterion for mandatory selector prefixes

This file instantiates the finite weighted Schur reduction at the exact
off-diagonal budget required by `DualFarBound`.  For any fixed affine prefix,
positive support weights and the displayed row-charge inequality imply the
small-seed selector-pair correlation target.

No weights are constructed here, and no machine-semantic argument for the
row inequality is assumed.  The result isolates that selector-specific
obligation without turning it into an opaque hypothesis or claiming an
unconditional correlation bound.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanFullIndependenceRestriction
open FiniteAffineRestrictionHybrid
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredWeightedCharge
open MandatoryCanonicalSelectorPairCorrelation

namespace MandatoryCanonicalSelectorWeightedCharge

/-- The exact positive-weight row-charge premise at one fixed affine prefix.
Its budget is precisely the portion left after the diagonal
`p^(2*m+1)` contribution. -/
def SelectorWeightedRowChargeBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (weight : Finset (Fin (2 ^ n)) → Rat) : Prop :=
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  (∀ support ∈ activeHighDegreeSupports (2 * m) f,
      0 < weight support) ∧
    ∀ left ∈ activeHighDegreeSupports (2 * m) f,
      weightedRowCharge (activeHighDegreeSupports (2 * m) f)
          (structuredPositivePairKernel n m tailBits hn htail f)
          weight left ≤
        ((1 - p) * p ^ (2 * m)) * weight left

/-- The weighted row-charge premise implies the existing exact
`DualFarBound` for the mandatory selector after the given affine prefix. -/
theorem dualFarBound_of_selectorWeightedRowChargeBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (weight : Finset (Fin (2 ^ n)) → Rat)
    (hcharge : SelectorWeightedRowChargeBound machine n T b m tailBits
      hn htail rounds weight) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity : (0 : Rat) < (2 : Rat) ^ tailBits)).2
    exact one_le_pow₀ (by norm_num : (1 : Rat) ≤ 2)
  have hbudget : 0 ≤ (1 - p) * p ^ (2 * m) :=
    mul_nonneg (sub_nonneg.mpr hp1) (pow_nonneg hp0 _)
  have hbounded : ∀ input, |f input| ≤ 1 := by
    intro input
    unfold f B FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have hcharge' := hcharge
  change
    (∀ support ∈ activeHighDegreeSupports (2 * m) f,
        0 < weight support) ∧
      ∀ left ∈ activeHighDegreeSupports (2 * m) f,
        weightedRowCharge (activeHighDegreeSupports (2 * m) f)
            (structuredPositivePairKernel n m tailBits hn htail f)
            weight left ≤
          ((1 - p) * p ^ (2 * m)) * weight left at hcharge'
  have hfar :
      structuredDualFarPairCorrelation n m tailBits (2 * m) hn htail f ≤
        (1 - p) * p ^ (2 * m) := by
    apply structuredDualFarPairCorrelation_le_positiveRowBudget
        n m tailBits (2 * m) hn htail f hbounded weight
          ((1 - p) * p ^ (2 * m)) hbudget
    · exact hcharge'.1
    · exact hcharge'.2
  simpa [DualFarBound, B, f, p] using hfar

/-! ## Exact generated-prefix obligation -/

/-- For an `L`-round hybrid, every generated affine prefix of depth `r < L`
admits its own positive weights satisfying the selector-dependent `E_f`
row-charge budget.  The existential weights may depend on both the prefix
depth and the fixed old seeds. -/
def GeneratedPrefixSelectorWeightedRowChargeBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits ≤ n) : Prop :=
  ∀ (r : Nat), r < L →
    ∀ oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      ∃ weight : Finset (Fin (2 ^ n)) → Rat,
        SelectorWeightedRowChargeBound machine n T b m tailBits hn htail
          (roundsOfSeeds
            (structuredUnbiasedPrimitive n m hn).generate
            (structuredDyadicPrimitive n m tailBits hn htail).generate
            r oldSeeds)
          weight

/-- Generated-prefix positive-edge row charges discharge the existing exact
generated-prefix `DualFarBoundUpTo` obligation. -/
theorem generatedPrefixDualFarBoundUpTo_of_selectorWeightedRowChargeBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits ≤ n)
    (hcharge : GeneratedPrefixSelectorWeightedRowChargeBoundUpTo
      machine n T b m tailBits L hn htail) :
    GeneratedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail := by
  intro r hr oldSeeds
  obtain ⟨weight, hweight⟩ := hcharge r hr oldSeeds
  exact dualFarBound_of_selectorWeightedRowChargeBound
    machine n T b m tailBits hn htail _ weight hweight

/-- The explicit generated-prefix positive-edge charge obligation is
sufficient for the card-free `L * p^m` Fourier hybrid error. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixSelectorWeightedRowChargeBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits ≤ n)
    (hcharge : GeneratedPrefixSelectorWeightedRowChargeBoundUpTo
      machine n T b m tailBits L hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| ≤ (L : Rat) * p ^ m := by
  exact
    abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail
        (generatedPrefixDualFarBoundUpTo_of_selectorWeightedRowChargeBoundUpTo
          machine n T b m tailBits L hn htail hcharge)

end MandatoryCanonicalSelectorWeightedCharge
end

end OneTapeMagnification
end Frontier
end Pnp4
