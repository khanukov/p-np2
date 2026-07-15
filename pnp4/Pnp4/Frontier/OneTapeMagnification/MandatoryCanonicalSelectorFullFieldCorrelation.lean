import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Full-field correlation for the mandatory canonical selector

The full-coordinate dyadic mask gives a size-free correlation theorem for
every bounded Boolean-cube function.  This file instantiates that theorem on
the mandatory canonical selector after each generated affine prefix and then
uses the exact selector-pair hybrid interface.

This closes the requested selector-pair lemma for `tailBits = n`.  It does not
close the magnification route: here `p = 2^-n`, so the terminal truth table
survives one round with marginal `1 - 2^-n`; removing it requires too many
rounds for the small fixed-seed DAG budget.
-/

noncomputable section

open FiniteAffineRestrictionHybrid
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredFullFieldCorrelation
open MandatoryCanonicalSelectorPairCorrelation

namespace MandatoryCanonicalSelectorFullFieldCorrelation

/-- The unconditional full-field correlation theorem proves the exact signed
`DualFarBound` for every affine prefix of the mandatory selector. -/
theorem dualFarBound_fullCoordinates
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m : Nat) (hn : 0 < n) (hm : 0 < m)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    DualFarBound machine n T b m n hn (Nat.le_refl n) rounds := by
  let f :=
    (prefixedMandatoryCanonicalSelector machine n T b rounds)
      |>.ratAcceptanceIndicator
  have hbounded : forall input, |f input| <= 1 := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  unfold DualFarBound
  dsimp only
  exact structuredDualFarPairCorrelation_full_le_dualFarBudget
    n m hn hm f hbounded

/-- Therefore the exact finite-depth generated-prefix obligation holds for
every number of full-field rounds. -/
theorem generatedPrefixDualFarBoundUpTo_fullCoordinates
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m L : Nat) (hn : 0 < n) (hm : 0 < m) :
    GeneratedPrefixDualFarBoundUpTo
      machine n T b m n L hn (Nat.le_refl n) := by
  apply generatedPrefixDualFarBoundUpTo_of_generatedPrefixDualFarBound
  apply generatedPrefixDualFarBound_of_allDualFarBounds
  intro rounds
  exact dualFarBound_fullCoordinates machine n T b m hn hm rounds

/-- Concrete card-free multi-round Fourier error for the mandatory selector
in the full-field regime.  The separate terminal-survivor cost is not included
in this statement. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_fullCoordinates
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m L : Nat) (hn : 0 < n) (hm : 0 < m) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask :=
      (structuredDyadicPrimitive n m n hn (Nat.le_refl n)).generate
    |value B D mask L - value B D mask 0| <=
      (L : Rat) * (1 / (2 : Rat) ^ n) ^ m := by
  exact
    abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBoundUpTo
      machine n T b m n L hn (Nat.le_refl n)
        (generatedPrefixDualFarBoundUpTo_fullCoordinates
          machine n T b m L hn hm)

end MandatoryCanonicalSelectorFullFieldCorrelation
end

end OneTapeMagnification
end Frontier
end Pnp4
