import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualRankThresholdBridge
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Hyperplane smoothing of the structured dual-rank form

This file rewrites the exact inverse-rank weight as a mixture of a terminal
constant and the survival probability of a uniformly chosen nonzero linear
functional.  The resulting proportional signed contraction is deliberately
left as a named `Prop`: the theorems below prove that this strong contraction,
together with the unconditional terminal estimate, is sufficient for the
existing `DualFarBound`.

It is not the exact remaining selector target.  The weaker necessary-and-
sufficient conditional-seed budget, including the actual signed terminal
form, is exposed in `FiniteStructuredDualNonzeroSeedCorrelation`.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open DPTWStructuredRankWeightedDualCorrelation
open FiniteAffineRestrictionHybrid
open MandatoryCanonicalSelectorPairCorrelation
open FiniteRankWeightAbelVariation
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualRankThresholdBridge

namespace FiniteStructuredDualHyperplaneContraction

/-! ## Exact hyperplane mixture -/

/-- Survival probability of a rank-`rank` subspace under a uniformly chosen
nonzero linear functional on an `upperRank`-dimensional binary space.

Only the range `rank <= upperRank` is used below.  The natural-number
subtraction keeps the definition total outside that range. -/
def hyperplaneSurvivalWeight (upperRank rank : Nat) : Rat :=
  ((2 : Rat) ^ (upperRank - rank) - 1) /
    ((2 : Rat) ^ upperRank - 1)

/-- Pointwise mixture identity.  For `rank <= upperRank`, inverse-rank
survival is a mixture of nonzero-hyperplane survival and the terminal atom. -/
theorem dyadicRankWeight_eq_hyperplane_mixture
    {upperRank rank : Nat} (hupperPos : 0 < upperRank)
    (hrank : rank <= upperRank) :
    dyadicRankWeight rank =
      (1 - dyadicRankWeight upperRank) *
          hyperplaneSurvivalWeight upperRank rank +
        dyadicRankWeight upperRank := by
  unfold dyadicRankWeight hyperplaneSurvivalWeight
  have hpow : (1 : Rat) < (2 : Rat) ^ upperRank := by
    exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hupperPos)
  have hden : (2 : Rat) ^ upperRank - 1 ≠ 0 := by linarith
  have htwo : (2 : Rat) ^ upperRank ≠ 0 := by positivity
  have hsplit :
      (2 : Rat) ^ (upperRank - rank) * (2 : Rat) ^ rank =
        (2 : Rat) ^ upperRank := by
    rw [← pow_add]
    congr 1
    omega
  field_simp [hden, htwo]
  linear_combination
    -(((2 : Rat) ^ upperRank - 1) * (2 : Rat) ^ upperRank) * hsplit

/-- The structured distinct-alias form with the hyperplane survival weight
in place of the inverse-rank weight. -/
def structuredDualHyperplaneSmoothedCrossForm
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) : Rat :=
  ∑ pair in structuredDualAliasPairs n m cutoff hn,
    hyperplaneSurvivalWeight (structuredIndependence m * n)
        (structuredDualAliasPairRank n m tailBits hn htail pair) *
      structuredDualAliasPairCoefficient leftFunction rightFunction pair

/-- Exact decomposition of the weighted distinct-alias form into the
hyperplane-smoothed form and its terminal unweighted coefficient sum. -/
theorem structuredDualRankDistinctCrossForm_eq_hyperplane_add_terminal
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction =
      (1 - dyadicRankWeight (structuredIndependence m * n)) *
          structuredDualHyperplaneSmoothedCrossForm
            n m tailBits cutoff hn htail leftFunction rightFunction +
        dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm
            n m tailBits cutoff hn htail leftFunction rightFunction
              (structuredIndependence m * n) := by
  classical
  rw [structuredDualRankDistinctCrossForm_eq_pairWeightedSum]
  rw [structuredDualRankAtMostCrossForm_terminal_eq_pairCoefficientSum]
  unfold structuredDualHyperplaneSmoothedCrossForm
  rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair hpair
  rw [dyadicRankWeight_eq_hyperplane_mixture
    (show 0 < structuredIndependence m * n by
      exact Nat.mul_pos (by unfold structuredIndependence; omega) hn)
    (structuredDualAliasPairRank_upper n m tailBits hn htail pair)]
  ring

/-- Self-specialization, stated directly for the exact weighted residual
used by the one-round selector argument. -/
theorem structuredRankWeightedDualFarPairCorrelation_eq_hyperplane_add_terminal
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f =
      (1 - dyadicRankWeight (structuredIndependence m * n)) *
          structuredDualHyperplaneSmoothedCrossForm
            n m tailBits cutoff hn htail f f +
        dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm
            n m tailBits cutoff hn htail f f
              (structuredIndependence m * n) := by
  rw [<- structuredDualRankDistinctCrossForm_self_eq_rankWeightedDualFar]
  exact structuredDualRankDistinctCrossForm_eq_hyperplane_add_terminal
    n m tailBits cutoff hn htail f f

/-! ## A strong sufficient signed contraction -/

/-- A strong proportional signed hyperplane contraction.  It is an upper
bound, not an absolute-value statement, and is not asserted here.  In
particular, it is stronger than the sharp affine conditional-seed budget in
`FiniteStructuredDualNonzeroSeedCorrelation`. -/
def StructuredDualHyperplaneContraction
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) : Prop :=
  structuredDualHyperplaneSmoothedCrossForm
      n m tailBits cutoff hn htail leftFunction rightFunction <=
    hyperplaneSurvivalWeight
        (structuredIndependence m * n)
        (structuredIndependence m * tailBits) *
      structuredDualRankAtMostCrossForm
        n m tailBits cutoff hn htail leftFunction rightFunction
          (structuredIndependence m * n)

theorem one_sub_dyadicRankWeight_nonneg
    (rank : Nat) :
    0 <= 1 - dyadicRankWeight rank := by
  unfold dyadicRankWeight
  have hpow : (1 : Rat) <= (2 : Rat) ^ rank := by
    exact one_le_pow₀ (by norm_num)
  have hpowPos : (0 : Rat) < (2 : Rat) ^ rank := by positivity
  rw [sub_nonneg, div_le_iff₀ hpowPos]
  simpa using hpow

/-- The signed contraction and a terminal cap imply the same sharp
`cap * 2^{-r0}` upper bound as a uniform cumulative-rank cap. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_cap_mul_baseWeight_of_hyperplaneContraction
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) (cap : Rat)
    (hcontraction : StructuredDualHyperplaneContraction
      n m tailBits cutoff hn htail f f)
    (hterminal :
      structuredDualRankAtMostCrossForm
        n m tailBits cutoff hn htail f f
          (structuredIndependence m * n) <= cap) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f <=
      cap * dyadicRankWeight (structuredIndependence m * tailBits) := by
  rw [structuredRankWeightedDualFarPairCorrelation_eq_hyperplane_add_terminal]
  let upperRank := structuredIndependence m * n
  let baseRank := structuredIndependence m * tailBits
  let terminal := structuredDualRankAtMostCrossForm
    n m tailBits cutoff hn htail f f upperRank
  have hupperPos : 0 < upperRank := by
    dsimp [upperRank]
    exact Nat.mul_pos (by unfold structuredIndependence; omega) hn
  have hbase : baseRank <= upperRank := by
    dsimp [baseRank, upperRank]
    exact Nat.mul_le_mul_left (structuredIndependence m) htail
  have hmixNonneg : 0 <= 1 - dyadicRankWeight upperRank :=
    one_sub_dyadicRankWeight_nonneg upperRank
  have hweightNonneg : 0 <= dyadicRankWeight baseRank :=
    dyadicRankWeight_nonneg baseRank
  calc
    (1 - dyadicRankWeight upperRank) *
          structuredDualHyperplaneSmoothedCrossForm
            n m tailBits cutoff hn htail f f +
        dyadicRankWeight upperRank * terminal <=
      (1 - dyadicRankWeight upperRank) *
          (hyperplaneSurvivalWeight upperRank baseRank * terminal) +
        dyadicRankWeight upperRank * terminal := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hcontraction hmixNonneg) _
    _ = dyadicRankWeight baseRank * terminal := by
      rw [dyadicRankWeight_eq_hyperplane_mixture hupperPos hbase]
      ring
    _ <= dyadicRankWeight baseRank * cap :=
      mul_le_mul_of_nonneg_left hterminal hweightNonneg
    _ = cap * dyadicRankWeight baseRank := by ring

/-- At cutoff `2m`, the signed hyperplane contraction and the unconditional
terminal-four estimate imply the existing exact dual-far budget. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_dualFarBudget_of_hyperplaneContraction
    (n m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1)
    (hcontraction : StructuredDualHyperplaneContraction
      n m tailBits (2 * m) hn htail f f) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits (2 * m) hn htail f <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
        (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  exact (structuredRankWeightedDualFarPairCorrelation_le_cap_mul_baseWeight_of_hyperplaneContraction
    n m tailBits (2 * m) hn htail f 4 hcontraction
      (structuredDualRankAtMostCrossForm_terminal_le_four
        n m tailBits hn htail f hbounded)).trans
    (four_mul_dyadicStructuredBaseWeight_le_dualFarBudget
      m tailBits hm htailPos)

/-- The same contraction controls the original structured dual-far
correlation after the exact rank-weight identification. -/
theorem structuredDualFarPairCorrelation_le_dualFarBudget_of_hyperplaneContraction
    (n m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1)
    (hcontraction : StructuredDualHyperplaneContraction
      n m tailBits (2 * m) hn htail f f) :
    structuredDualFarPairCorrelation n m tailBits (2 * m) hn htail f <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
        (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  exact structuredRankWeightedDualFarPairCorrelation_le_dualFarBudget_of_hyperplaneContraction
    n m tailBits hn hm htailPos htail f hbounded hcontraction

/-! ## Mandatory-selector specializations -/

/-- For one actual affine prefix of the mandatory selector, the signed
hyperplane contraction is sufficient for `DualFarBound`. -/
theorem dualFarBound_of_structuredDualHyperplaneContraction
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hcontraction : StructuredDualHyperplaneContraction
      n m tailBits (2 * m) hn htail
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  unfold DualFarBound
  exact structuredDualFarPairCorrelation_le_dualFarBudget_of_hyperplaneContraction
    n m tailBits hn hm htailPos htail B.ratAcceptanceIndicator
      (by
        intro input
        classical
        by_cases haccepts : B.Accepts input <;>
          simp [FiniteUnambiguousFBDD.ratAcceptanceIndicator, haccepts])
      hcontraction

/-- The contraction obligation restricted to prefixes actually generated
by the structured hybrid. -/
def GeneratedPrefixStructuredDualHyperplaneContraction
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n) : Prop :=
  forall (r : Nat)
    (oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r),
    StructuredDualHyperplaneContraction
      n m tailBits (2 * m) hn htail
        (prefixedMandatoryCanonicalSelector machine n T b
          (roundsOfSeeds
            (structuredUnbiasedPrimitive n m hn).generate
            (structuredDyadicPrimitive n m tailBits hn htail).generate
            r oldSeeds)).ratAcceptanceIndicator
        (prefixedMandatoryCanonicalSelector machine n T b
          (roundsOfSeeds
            (structuredUnbiasedPrimitive n m hn).generate
            (structuredDyadicPrimitive n m tailBits hn htail).generate
            r oldSeeds)).ratAcceptanceIndicator

/-- Generated-prefix hyperplane contraction implies the exact existing
generated-prefix dual-far interface. -/
theorem generatedPrefixDualFarBound_of_structuredDualHyperplaneContraction
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (hcontraction : GeneratedPrefixStructuredDualHyperplaneContraction
      machine n T b m tailBits hn htail) :
    GeneratedPrefixDualFarBound machine n T b m tailBits hn htail := by
  intro r oldSeeds
  exact dualFarBound_of_structuredDualHyperplaneContraction
    machine n T b m tailBits hn hm htailPos htail _
      (hcontraction r oldSeeds)

end FiniteStructuredDualHyperplaneContraction
end

end OneTapeMagnification
end Frontier
end Pnp4
