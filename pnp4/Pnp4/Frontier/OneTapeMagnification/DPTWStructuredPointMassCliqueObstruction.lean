import Pnp4.Frontier.OneTapeMagnification.FiniteWeightedChargeCliqueObstruction
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorWeightedCharge
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A point-mass clique obstruction for the structured positive kernel

This file gives a concrete Fourier-level counterexample to the positive
weighted-row-charge criterion.  On four Boolean coordinates, take the point
mass at the all-false input, `m = 0`, and one mask-prefix bit.  Four explicit
two-point Fourier supports form a positive clique.  Every off-diagonal edge
has weight at least `1/4`, while the requested selector budget is `1/2`.
Consequently no positive Schur weights exist.

This does not by itself exhibit a one-tape machine whose mandatory canonical
selector is exactly the point mass.  The final theorem therefore states that
machine-level consequence with the semantic equality as an explicit premise.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanFullIndependenceRestriction
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open DPTWStructuredRankWeightedDualCorrelation
open DPTWStructuredWeightedCharge
open FiniteWeightedChargeCliqueObstruction
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorWeightedCharge

namespace DPTWStructuredPointMassCliqueObstruction

local instance pointMassDualSupportDecidable
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    Decidable (IsStructuredDualSupport n k hn support) :=
  Classical.propDecidable _

/-- Indicator of the all-false point of a finite Boolean cube. -/
def zeroPointIndicator (coordinateCount : Nat)
    (input : Fin coordinateCount -> Bool) : Rat :=
  if input = fun _ => false then 1 else 0

/-- Every Walsh coefficient of the all-false point mass is the same positive
number. -/
theorem coefficient_zeroPointIndicator
    (coordinateCount : Nat) (support : Finset (Fin coordinateCount)) :
    coefficient (zeroPointIndicator coordinateCount) support =
      1 / (2 : Rat) ^ coordinateCount := by
  classical
  unfold coefficient zeroPointIndicator
  congr 1
  calc
    (∑ input : Fin coordinateCount -> Bool,
        (if input = (fun _ => false) then 1 else 0) *
          character support input) =
      (if (fun _ : Fin coordinateCount => false) = (fun _ => false)
        then 1 else 0) * character support (fun _ => false) := by
          apply Fintype.sum_eq_single (fun _ => false)
          intro input hinput
          simp [hinput]
    _ = 1 := by simp [character]

abbrev FourCoordinate := Fin (2 ^ 2)

def support01 : Finset FourCoordinate := {0, 1}
def support02 : Finset FourCoordinate := {0, 2}
def support03 : Finset FourCoordinate := {0, 3}
def support12 : Finset FourCoordinate := {1, 2}

/-- Four supports used for the explicit clique. -/
def pointMassClique : Finset (Finset FourCoordinate) :=
  {support01, support02, support03, support12}

theorem pointMassClique_nonempty : pointMassClique.Nonempty := by
  exact ⟨support01, by simp [pointMassClique]⟩

theorem pointMassClique_card : pointMassClique.card = 4 := by
  decide

/-- Every nonempty Fourier support of the all-false point mass is active at
cutoff zero. -/
theorem mem_activeHighDegreeSupports_zeroPointIndicator_of_nonempty
    (support : Finset FourCoordinate) (hnonempty : support.Nonempty) :
    support ∈ activeHighDegreeSupports 0 (zeroPointIndicator (2 ^ 2)) := by
  change support ∈
    activeIndices (highDegreeSupports (2 ^ 2) 0)
      (coefficient (zeroPointIndicator (2 ^ 2)))
  rw [mem_activeIndices]
  constructor
  · rw [mem_highDegreeSupports]
    exact Finset.card_pos.mpr hnonempty
  · rw [coefficient_zeroPointIndicator]
    norm_num

theorem pointMassClique_subset_activeHighDegreeSupports :
    pointMassClique ⊆
      activeHighDegreeSupports 0 (zeroPointIndicator (2 ^ 2)) := by
  intro support hsupport
  apply mem_activeHighDegreeSupports_zeroPointIndicator_of_nonempty
  simp only [pointMassClique, Finset.mem_insert, Finset.mem_singleton] at hsupport
  rcases hsupport with rfl | rfl | rfl | rfl <;>
    simp [support01, support02, support03, support12]

/-- At polynomial degree one the only parity check is even support
cardinality.  We only need the forward implication here. -/
theorem isStructuredDualSupport_degreeOne_of_even_card
    (n : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (heven : Even support.card) :
    IsStructuredDualSupport n 1 hn support := by
  rw [isStructuredDualSupport_iff_powerSums_eq_zero]
  intro exponent
  fin_cases exponent
  unfold structuredSupportPowerSum
  simp only [pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  obtain ⟨half, hhalf⟩ := heven
  rw [hhalf, Nat.cast_add]
  have htwo : (2 : GaloisField 2 n) = 0 :=
    CharP.cast_eq_zero (GaloisField 2 n) 2
  calc
    (half : GaloisField 2 n) + half =
        (2 : GaloisField 2 n) * half := by ring
    _ = 0 := by rw [htwo, zero_mul]

/-- Distinct members of the explicit clique differ by a nonzero degree-one
dual support, hence satisfy the exact far-dual predicate in the kernel. -/
theorem pointMassClique_pair_far_dual
    (left right : Finset FourCoordinate)
    (hleft : left ∈ pointMassClique) (hright : right ∈ pointMassClique)
    (hne : left ≠ right) :
    structuredIndependence 0 < (left ∆ right).card ∧
      IsStructuredDualSupport 2 (structuredIndependence 0) (by omega)
        (left ∆ right) := by
  simp only [pointMassClique, Finset.mem_insert, Finset.mem_singleton] at hleft hright
  rcases hleft with rfl | rfl | rfl | rfl <;>
    rcases hright with rfl | rfl | rfl | rfl
  all_goals try { exact (hne rfl).elim }
  all_goals
    constructor
    · decide
    · exact isStructuredDualSupport_degreeOne_of_even_card 2 (by omega) _
        (by decide)

/-- Every off-diagonal edge of the explicit point-mass clique has structured
positive-kernel weight at least `1/4`.  The bound uses only the general rank
upper bound `rank <= k*n = 2`; no finite-field computation is hidden here. -/
theorem pointMassClique_kernel_ge_quarter
    (left right : Finset FourCoordinate)
    (hleft : left ∈ pointMassClique) (hright : right ∈ pointMassClique)
    (hne : left ≠ right) :
    (1 / 4 : Rat) <=
      structuredPositivePairKernel 2 0 1 (by omega) (by omega)
        (zeroPointIndicator (2 ^ 2)) left right := by
  have hcoefficientPositive (support : Finset FourCoordinate) :
      0 < coefficient (zeroPointIndicator (2 ^ 2)) support := by
    rw [coefficient_zeroPointIndicator]
    norm_num
  unfold structuredPositivePairKernel
  rw [if_pos (mul_pos (hcoefficientPositive left)
    (hcoefficientPositive right))]
  unfold structuredDualRankKernel
  have hfarDual := pointMassClique_pair_far_dual
    left right hleft hright hne
  rw [if_pos ⟨hne, hfarDual.1, hfarDual.2⟩]
  have hrank := supportPrefixConstraintRank_upperBound
    2 (structuredIndependence 0) 1 (by omega) (by omega) (left ∪ right)
  norm_num [structuredIndependence] at hrank
  interval_cases h : supportPrefixConstraintRank 2 1 1 (by omega) (by omega)
      (left ∪ right)
  all_goals
    rw [show structuredIndependence 0 = 1 by rfl, h]
    norm_num

/-- The exact positive-row criterion fails for the all-false point mass on
four coordinates.  This quantifies over every positive rational weight, so
it rules out residual-mass and last-prefix choices as special cases. -/
theorem no_positiveRowChargeWeights_zeroPointIndicator :
    ¬ ∃ weight : Finset FourCoordinate -> Rat,
        (∀ support ∈
            activeHighDegreeSupports 0 (zeroPointIndicator (2 ^ 2)),
          0 < weight support) ∧
        ∀ left ∈
            activeHighDegreeSupports 0 (zeroPointIndicator (2 ^ 2)),
          weightedRowCharge
              (activeHighDegreeSupports 0 (zeroPointIndicator (2 ^ 2)))
              (structuredPositivePairKernel 2 0 1 (by omega) (by omega)
                (zeroPointIndicator (2 ^ 2)))
              weight left <= (1 / 2 : Rat) * weight left := by
  rintro ⟨weight, hweight, hrow⟩
  have hnecessary :=
    card_sub_one_mul_edgeFloor_le_budget_of_subset
      pointMassClique
      (activeHighDegreeSupports 0 (zeroPointIndicator (2 ^ 2)))
      (structuredPositivePairKernel 2 0 1 (by omega) (by omega)
        (zeroPointIndicator (2 ^ 2)))
      weight (1 / 4 : Rat) (1 / 2 : Rat)
      pointMassClique_nonempty pointMassClique_subset_activeHighDegreeSupports
      hweight
      (by
        intro left _hleft right _hright
        exact structuredPositivePairKernel_nonnegative
          2 0 1 (by omega) (by omega)
            (zeroPointIndicator (2 ^ 2)) left right)
      (by
        intro left hleft right hright hne
        exact pointMassClique_kernel_ge_quarter
          left right hleft hright hne)
      hrow
  rw [pointMassClique_card] at hnecessary
  norm_num at hnecessary

theorem highDegreeSupports_four_zero_card :
    (highDegreeSupports (2 ^ 2) 0).card = 15 := by
  decide

/-- Each ordered high-support pair contributes at most `1/512` to the exact
rank-weighted residual.  This intentionally keeps even the zero terms and
the diagonal, making the later counting argument elementary. -/
theorem pointMass_rankWeightedPairTerm_le
    (left right : Finset FourCoordinate)
    (hleft : left ∈ highDegreeSupports (2 ^ 2) 0)
    (_hright : right ∈ highDegreeSupports (2 ^ 2) 0) :
    (if left ≠ right ∧
          structuredIndependence 0 < (left ∆ right).card ∧
          IsStructuredDualSupport 2 (structuredIndependence 0) (by omega)
            (left ∆ right) then
        coefficient (zeroPointIndicator (2 ^ 2)) left *
          coefficient (zeroPointIndicator (2 ^ 2)) right *
          (1 / (2 : Rat) ^
            supportPrefixConstraintRank 2 (structuredIndependence 0) 1
              (by omega) (by omega) (left ∪ right))
      else 0) <= (1 / 512 : Rat) := by
  by_cases hpair : left ≠ right ∧
      structuredIndependence 0 < (left ∆ right).card ∧
      IsStructuredDualSupport 2 (structuredIndependence 0) (by omega)
        (left ∆ right)
  · rw [if_pos hpair, coefficient_zeroPointIndicator,
      coefficient_zeroPointIndicator]
    have hleftCard : 1 <= left.card := by
      have := mem_highDegreeSupports.mp hleft
      omega
    have hunionCard : 1 <= (left ∪ right).card :=
      hleftCard.trans (Finset.card_le_card Finset.subset_union_left)
    have hlower : 1 <=
        supportPrefixConstraintRank 2 1 1 (by omega) (by omega)
          (left ∪ right) := by
      simpa using supportPrefixConstraintRank_lowerBound
        2 1 1 (by omega) (by omega) (left ∪ right) hunionCard
    have hupper :
        supportPrefixConstraintRank 2 1 1 (by omega) (by omega)
          (left ∪ right) <= 2 := by
      simpa using supportPrefixConstraintRank_upperBound
        2 1 1 (by omega) (by omega) (left ∪ right)
    interval_cases hrank :
        supportPrefixConstraintRank 2 1 1 (by omega) (by omega)
          (left ∪ right)
    all_goals
      rw [show structuredIndependence 0 = 1 by rfl, hrank]
      norm_num
  · rw [if_neg hpair]
    norm_num

/-- The point mass refutes the uniform positive-row certificate but not the
target correlation inequality itself: its exact signed dual-far residual is
strictly below the required `1/2` budget. -/
theorem structuredDualFarPairCorrelation_zeroPointIndicator_le_half :
    structuredDualFarPairCorrelation 2 0 1 0 (by omega) (by omega)
        (zeroPointIndicator (2 ^ 2)) <= (1 / 2 : Rat) := by
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  unfold structuredRankWeightedDualFarPairCorrelation
  calc
    (∑ left ∈ highDegreeSupports (2 ^ 2) 0,
        ∑ right ∈ highDegreeSupports (2 ^ 2) 0,
          if left ≠ right ∧
              structuredIndependence 0 < (left ∆ right).card ∧
              IsStructuredDualSupport 2 (structuredIndependence 0) (by omega)
                (left ∆ right) then
            coefficient (zeroPointIndicator (2 ^ 2)) left *
              coefficient (zeroPointIndicator (2 ^ 2)) right *
              (1 / (2 : Rat) ^
                supportPrefixConstraintRank 2 (structuredIndependence 0) 1
                  (by omega) (by omega) (left ∪ right))
          else 0) <=
        ∑ _left ∈ highDegreeSupports (2 ^ 2) 0,
          ∑ _right ∈ highDegreeSupports (2 ^ 2) 0, (1 / 512 : Rat) := by
      apply Finset.sum_le_sum
      intro left hleft
      apply Finset.sum_le_sum
      intro right hright
      exact pointMass_rankWeightedPairTerm_le left right hleft hright
    _ = (225 / 512 : Rat) := by
      simp only [Finset.sum_const, nsmul_eq_mul,
        highDegreeSupports_four_zero_card]
      norm_num
    _ <= (1 / 2 : Rat) := by norm_num

/-- Machine-level conditional consequence.  If a generated mandatory
selector prefix has singleton all-false acceptance semantics, then the
current `SelectorWeightedRowChargeBound` premise is false at
`n = 2, m = 0, tailBits = 1`.  The semantic realization premise is kept
explicit rather than being attributed to the canonical construction. -/
theorem not_selectorWeightedRowChargeBound_of_zeroPointIndicator
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) (rounds : List (AffineRestrictionRound (2 ^ 2)))
    (hpoint :
      (prefixedMandatoryCanonicalSelector machine 2 T b rounds).ratAcceptanceIndicator =
        zeroPointIndicator (2 ^ 2))
    (weight : Finset FourCoordinate -> Rat) :
    ¬ SelectorWeightedRowChargeBound machine 2 T b 0 1
        (by omega) (by omega) rounds weight := by
  intro hcharge
  apply no_positiveRowChargeWeights_zeroPointIndicator
  refine ⟨weight, ?_⟩
  norm_num [SelectorWeightedRowChargeBound, hpoint] at hcharge ⊢
  exact hcharge

end DPTWStructuredPointMassCliqueObstruction
end

end OneTapeMagnification
end Frontier
end Pnp4
