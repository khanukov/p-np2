import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredMaskRank

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Rank-weighted form of the structured dual correlation

The unbiased structured source restricts the far Fourier residual to pairs
whose symmetric difference lies in its explicit dual code.  Independently,
the dyadic mask survives on a union support with probability exactly two to
the negative rank of its prefix-constraint map.  This file combines those two
facts without taking absolute values or replacing the rank by its generic
lower bound.

The resulting finite signed quadratic form is the concrete general-tail
selector-correlation target.  This identity does not bound that form and is
not by itself progress on a mainline lower-bound source.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanFullIndependenceRestriction
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank

namespace DPTWStructuredRankWeightedDualCorrelation

/-- The exact dual-code far residual with every mask factor exposed as the
inverse power of the actual union-support constraint rank. -/
def structuredRankWeightedDualFarPairCorrelation
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) : Rat := by
  classical
  exact
    ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
      ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
        if left ≠ right ∧
            structuredIndependence m < (left ∆ right).card ∧
            IsStructuredDualSupport n (structuredIndependence m) hn
              (left ∆ right) then
          coefficient f left * coefficient f right *
            (1 / (2 : Rat) ^
              supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail (left ∪ right))
        else 0

/-- Exact combination of the dual-code character law and the mask-rank law.
No triangle inequality, coefficient-mass estimate, or rank relaxation occurs
in this rewrite. -/
theorem structuredDualFarPairCorrelation_eq_rankWeighted
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    structuredDualFarPairCorrelation n m tailBits cutoff hn htail f =
      structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f := by
  classical
  unfold structuredDualFarPairCorrelation
    structuredRankWeightedDualFarPairCorrelation
  apply Finset.sum_congr rfl
  intro left _hleft
  apply Finset.sum_congr rfl
  intro right _hright
  by_cases hpair : left ≠ right ∧
      structuredIndependence m < (left ∆ right).card ∧
      IsStructuredDualSupport n (structuredIndependence m) hn
        (left ∆ right)
  · rw [if_pos hpair, if_pos hpair,
      structuredDyadicPrimitive_maskSurvival_eq_invPowRank]
  · rw [if_neg hpair, if_neg hpair]

end DPTWStructuredRankWeightedDualCorrelation
end

end OneTapeMagnification
end Frontier
end Pnp4
