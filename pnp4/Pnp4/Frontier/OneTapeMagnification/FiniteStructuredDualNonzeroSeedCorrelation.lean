import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualHyperplaneContraction
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorRankDispersion
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Nonzero-seed semantics of structured dual hyperplane smoothing

The hyperplane survival weight is the exact conditional survival probability
of the structured dyadic mask after removing its all-zero coefficient seed.
This file proves that statement on the concrete seed type
`FiniteBitTape ((4m+1)n)`, commutes the conditional average through the
structured dual-pair sum, and exposes the resulting mandatory-selector
correlation obligation.

The resulting conditional mask-seed identity gives an exact characterization
of the existing `DualFarBound`; no equivalent wrapper proposition is added.
The numerical selector inequality in that characterization remains unproved.
The earlier `StructuredDualHyperplaneContraction` is a strictly stronger
sufficient condition and is not treated here as the exact selector target.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanFourierEnergy
open GaloisBilinearTensorBridge
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open DPTWStructuredRankWeightedDualCorrelation
open DPTWStructuredFullFieldCorrelation
open FiniteAffineRestrictionHybrid
open MandatoryCanonicalSelectorPairCorrelation
open FiniteRankWeightAbelVariation
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualRankThresholdBridge
open FiniteStructuredDualHyperplaneContraction
open MandatoryCanonicalSelectorRankDispersion

namespace FiniteStructuredDualNonzeroSeedCorrelation

/-! ## Exact conditional average on nonzero bit seeds -/

/-- The all-zero Boolean coefficient seed. -/
def zeroBitSeed (seedBits : Nat) : FiniteBitTape seedBits :=
  fun _ => false

/-- All Boolean seeds except the all-zero coefficient seed. -/
def nonzeroBitSeeds (seedBits : Nat) : Finset (FiniteBitTape seedBits) :=
  Finset.univ.erase (zeroBitSeed seedBits)

theorem card_nonzeroBitSeeds (seedBits : Nat) :
    (nonzeroBitSeeds seedBits).card = 2 ^ seedBits - 1 := by
  classical
  simp [nonzeroBitSeeds]

/-- Uniform conditional average over the nonzero Boolean seeds, written with
the explicit denominator `2^seedBits - 1`. -/
def nonzeroBitSeedAverage (seedBits : Nat)
    (value : FiniteBitTape seedBits -> Rat) : Rat :=
  (∑ seed ∈ nonzeroBitSeeds seedBits, value seed) /
    ((2 : Rat) ^ seedBits - 1)

/-- Splitting the complete bit-seed average into the zero seed and the
conditional nonzero-seed average gives the exact two-component mixture. -/
theorem finiteAverage_eq_nonzeroBitSeed_mixture
    (seedBits : Nat) (hseedBits : 0 < seedBits)
    (value : FiniteBitTape seedBits -> Rat) :
    finiteAverage value =
      (1 - dyadicRankWeight seedBits) *
          nonzeroBitSeedAverage seedBits value +
        dyadicRankWeight seedBits * value (zeroBitSeed seedBits) := by
  classical
  have hpow : (1 : Rat) < (2 : Rat) ^ seedBits :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hseedBits)
  have hpowNe : (2 : Rat) ^ seedBits ≠ 0 := by positivity
  have hdenNe : (2 : Rat) ^ seedBits - 1 ≠ 0 := by linarith
  unfold finiteAverage nonzeroBitSeedAverage nonzeroBitSeeds
    dyadicRankWeight
  rw [finiteBitTape_card]
  push_cast
  rw [← Finset.add_sum_erase Finset.univ value
    (Finset.mem_univ (zeroBitSeed seedBits))]
  field_simp [hpowNe, hdenNe]
  ring

theorem nonzeroBitSeedAverage_finset_sum
    {Index : Type*} [DecidableEq Index]
    (seedBits : Nat) (indices : Finset Index)
    (value : Index -> FiniteBitTape seedBits -> Rat) :
    nonzeroBitSeedAverage seedBits
        (fun seed => ∑ index ∈ indices, value index seed) =
      ∑ index ∈ indices,
        nonzeroBitSeedAverage seedBits (value index) := by
  classical
  unfold nonzeroBitSeedAverage
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

theorem nonzeroBitSeedAverage_congr
    (seedBits : Nat)
    (left right : FiniteBitTape seedBits -> Rat)
    (heq : ∀ seed ∈ nonzeroBitSeeds seedBits,
      left seed = right seed) :
    nonzeroBitSeedAverage seedBits left =
      nonzeroBitSeedAverage seedBits right := by
  unfold nonzeroBitSeedAverage
  congr 1
  exact Finset.sum_congr rfl heq

theorem nonzeroBitSeedAverage_sub
    (seedBits : Nat)
    (left right : FiniteBitTape seedBits -> Rat) :
    nonzeroBitSeedAverage seedBits (fun seed => left seed - right seed) =
      nonzeroBitSeedAverage seedBits left -
        nonzeroBitSeedAverage seedBits right := by
  unfold nonzeroBitSeedAverage
  rw [Finset.sum_sub_distrib]
  ring

theorem nonzeroBitSeedAverage_mul_const
    (seedBits : Nat) (value : FiniteBitTape seedBits -> Rat)
    (constant : Rat) :
    nonzeroBitSeedAverage seedBits
        (fun seed => value seed * constant) =
      nonzeroBitSeedAverage seedBits value * constant := by
  unfold nonzeroBitSeedAverage
  rw [← Finset.sum_mul]
  ring

theorem nonzeroBitSeedAverage_le_of_pointwise
    (seedBits : Nat) (hseedBits : 0 < seedBits)
    (value : FiniteBitTape seedBits -> Rat) (cap : Rat)
    (hvalue : ∀ seed ∈ nonzeroBitSeeds seedBits, value seed <= cap) :
    nonzeroBitSeedAverage seedBits value <= cap := by
  have hpow : (1 : Rat) < (2 : Rat) ^ seedBits :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hseedBits)
  have hdenPos : (0 : Rat) < (2 : Rat) ^ seedBits - 1 := by linarith
  unfold nonzeroBitSeedAverage
  apply (div_le_iff₀ hdenPos).mpr
  calc
    (∑ seed ∈ nonzeroBitSeeds seedBits, value seed) <=
        ∑ _seed ∈ nonzeroBitSeeds seedBits, cap := by
      exact Finset.sum_le_sum fun seed hseed => hvalue seed hseed
    _ = ((nonzeroBitSeeds seedBits).card : Rat) * cap := by simp
    _ = ((2 : Rat) ^ seedBits - 1) * cap := by
      have hpowNat : 1 <= 2 ^ seedBits :=
        Nat.one_le_pow seedBits 2 (by decide)
      rw [card_nonzeroBitSeeds, Nat.cast_sub hpowNat]
      norm_num
    _ = cap * ((2 : Rat) ^ seedBits - 1) := by ring

theorem one_sub_dyadicRankWeight_pos_of_pos
    {rank : Nat} (hrank : 0 < rank) :
    0 < 1 - dyadicRankWeight rank := by
  unfold dyadicRankWeight
  have hpow : (1 : Rat) < (2 : Rat) ^ rank :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hrank)
  have hpowPos : (0 : Rat) < (2 : Rat) ^ rank := by positivity
  rw [sub_pos, div_lt_one hpowPos]
  exact hpow

/-! ## The nonzero structured seed has exactly the hyperplane law -/

/-- The explicit coefficient-layout equivalence sends the all-zero Boolean
seed to the zero bounded-degree polynomial. -/
theorem structuredPolynomialBitSeedEquiv_zeroBitSeed
    (k n : Nat) (hn : n ≠ 0) :
    structuredPolynomialBitSeedEquiv k n hn (zeroBitSeed (k * n)) = 0 := by
  apply (Polynomial.degreeLTEquiv (GaloisField 2 n) k).injective
  funext coefficient
  rw [structuredPolynomialBitSeedEquiv_coefficient]
  apply (gfTwoBoolCoordinates n hn).injective
  rw [Equiv.apply_symm_apply]
  funext bit
  simp [zeroBitSeed, gfTwoBoolCoordinates_apply]

/-- Every support survives the all-zero coefficient seed. -/
theorem structuredDyadicPrimitive_zeroBitSeed_maskSurvival
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n))) :
    maskAllZeroIndicator support
        ((structuredDyadicPrimitive n m tailBits hn htail).generate
          (zeroBitSeed (structuredIndependence m * n))) = 1 := by
  rw [structuredDyadicPrimitive_generate n m tailBits hn htail]
  unfold structuredPolynomialSubsetSource
  rw [maskAllZeroIndicator_polynomialSubsetSource_eq_kernelIndicator
    n (structuredIndependence m) tailBits hn htail support]
  rw [if_pos]
  rw [structuredPolynomialBitSeedEquiv_zeroBitSeed
    (structuredIndependence m) n (Nat.ne_of_gt hn)]
  exact LinearMap.map_zero _

/-- Conditional on a nonzero structured coefficient seed, the exact mask
survival probability of `support` is the hyperplane survival weight at its
actual prefix-constraint rank. -/
theorem structuredDyadicPrimitive_nonzeroSeed_maskSurvival_eq_hyperplaneWeight
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n))) :
    nonzeroBitSeedAverage (structuredIndependence m * n)
        (fun seed : FiniteBitTape (structuredIndependence m * n) =>
          maskAllZeroIndicator support
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) =
      hyperplaneSurvivalWeight
        (structuredIndependence m * n)
        (supportPrefixConstraintRank n (structuredIndependence m)
          tailBits hn htail support) := by
  let upperRank := structuredIndependence m * n
  let rank := supportPrefixConstraintRank n (structuredIndependence m)
    tailBits hn htail support
  let survival : FiniteBitTape upperRank -> Rat := fun seed =>
    maskAllZeroIndicator support
      ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)
  have hupperPos : 0 < upperRank := by
    dsimp [upperRank]
    exact Nat.mul_pos (by unfold structuredIndependence; omega) hn
  have hrank : rank <= upperRank := by
    dsimp [rank, upperRank]
    exact supportPrefixConstraintRank_upperBound
      n (structuredIndependence m) tailBits hn htail support
  have hfull : finiteAverage survival = dyadicRankWeight rank := by
    dsimp [survival, rank, upperRank, dyadicRankWeight]
    exact structuredDyadicPrimitive_maskSurvival_eq_invPowRank
      n m tailBits hn htail support
  have hzero : survival (zeroBitSeed upperRank) = 1 := by
    dsimp [survival, upperRank]
    exact structuredDyadicPrimitive_zeroBitSeed_maskSurvival
      n m tailBits hn htail support
  have hmixture := finiteAverage_eq_nonzeroBitSeed_mixture
    upperRank hupperPos survival
  have hpoint := dyadicRankWeight_eq_hyperplane_mixture hupperPos hrank
  rw [hfull, hzero, mul_one] at hmixture
  have hfactorNe : 1 - dyadicRankWeight upperRank ≠ 0 :=
    (one_sub_dyadicRankWeight_pos_of_pos hupperPos).ne'
  apply mul_left_cancel₀ hfactorNe
  linarith [hmixture, hpoint]

/-! ## Semantic structured dual-pair correlation -/

/-- The signed structured dual-alias pair sum surviving one concrete mask. -/
def structuredDualPairCorrelationAtMask
    (n m cutoff : Nat) (hn : 0 < n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  ∑ pair ∈ structuredDualAliasPairs n m cutoff hn,
    maskAllZeroIndicator (pair.1 ∪ pair.2) mask *
      structuredDualAliasPairCoefficient leftFunction rightFunction pair

/-- For a self-pair, the concrete mask-facing sum is literally the generic
high-tail far-pair correlation with the structured unbiased base source and
the displayed mask as a one-point mask distribution. -/
theorem structuredDualPairCorrelationAtMask_self_eq_highTailFarPairCorrelation
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredDualPairCorrelationAtMask n m cutoff hn f f mask =
      highTailFarPairCorrelation f cutoff (structuredIndependence m)
        (structuredUnbiasedPrimitive n m hn).generate
        (fun _ : Unit => mask) := by
  classical
  unfold structuredDualPairCorrelationAtMask structuredDualAliasPairs
    structuredDualAliasPairCoefficient highTailFarPairCorrelation
  rw [Finset.sum_filter]
  refine (Finset.sum_product
    (highDegreeSupports (2 ^ n) cutoff)
    (highDegreeSupports (2 ^ n) cutoff)
    (fun pair =>
      if pair.1 ≠ pair.2 ∧
          IsStructuredDualSupport n (structuredIndependence m) hn
            (pair.1 ∆ pair.2) then
        maskAllZeroIndicator (pair.1 ∪ pair.2) mask *
          (coefficient f pair.1 * coefficient f pair.2)
      else 0)).trans ?_
  apply Finset.sum_congr rfl
  intro left hleft
  apply Finset.sum_congr rfl
  intro right hright
  by_cases hne : left ≠ right
  · by_cases hdual : IsStructuredDualSupport n (structuredIndependence m) hn
        (left ∆ right)
    · have hfar : structuredIndependence m < (left ∆ right).card :=
        structuredIndependence_lt_symmDiff_card_of_distinct_dual
          n m hn left right hne hdual
      rw [if_pos ⟨hne, hdual⟩, if_pos ⟨hne, hfar⟩]
      rw [structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq
        n m hn (fun _ : Unit => mask) left right]
      simp [hdual, finiteAverage]
      ring
    · rw [if_neg (by simp [hdual])]
      by_cases hfar : structuredIndependence m < (left ∆ right).card
      · rw [if_pos ⟨hne, hfar⟩]
        rw [structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq
          n m hn (fun _ : Unit => mask) left right]
        simp [hdual]
      · rw [if_neg (by simp [hfar])]
  · simp [hne]

/-- At one fixed mask, the structured signed pair correlation is exactly the
off-diagonal term in the restriction second moment.  Keeping the mask fixed
is what permits the later conditional average to exclude the zero seed. -/
theorem structured_fixedMask_highTail_secondMoment_eq_diagonal_add_pairCorrelation
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    finiteAverage
        (fun baseSeed : FiniteBitTape (structuredIndependence m * n) =>
          (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
            FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
              (maskedInput
                ((structuredUnbiasedPrimitive n m hn).generate baseSeed)
                mask uniform))) ^ 2) =
      (∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
        (coefficient f support) ^ 2 *
          maskAllZeroIndicator support mask) +
        structuredDualPairCorrelationAtMask n m (2 * m) hn f f mask := by
  have hsplit :=
    highTail_restriction_secondMoment_eq_diagonal_add_far
      (cutoff := 2 * m) (q := structuredIndependence m)
      f (structuredUnbiasedPrimitive n m hn).generate
        (fun _ : Unit => mask)
        (structuredUnbiasedPrimitive_patternUnbiased n m hn)
  have hlhs :
      finiteAverage
          (fun seed :
              FiniteBitTape (structuredIndependence m * n) × Unit =>
            (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
              FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
                (maskedInput
                  ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                  mask uniform))) ^ 2) =
        finiteAverage
          (fun baseSeed : FiniteBitTape (structuredIndependence m * n) =>
            (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
              FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
                (maskedInput
                  ((structuredUnbiasedPrimitive n m hn).generate baseSeed)
                  mask uniform))) ^ 2) := by
    change finiteAverage
        (fun seed :
            FiniteBitTape (structuredIndependence m * n) × Unit =>
          (fun left : FiniteBitTape (structuredIndependence m * n) =>
            fun _right : Unit =>
              (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
                FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
                  (maskedInput
                    ((structuredUnbiasedPrimitive n m hn).generate left)
                    mask uniform))) ^ 2) seed.1 seed.2) = _
    rw [finiteAverage_prod_eq_iterated
      (fun left : FiniteBitTape (structuredIndependence m * n) =>
        fun _right : Unit =>
          (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
            FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
              (maskedInput
                ((structuredUnbiasedPrimitive n m hn).generate left)
                mask uniform))) ^ 2)]
    apply finiteAverage_congr
    intro baseSeed
    simp [finiteAverage]
  rw [hlhs] at hsplit
  rw [← structuredDualPairCorrelationAtMask_self_eq_highTailFarPairCorrelation
    n m (2 * m) hn f mask] at hsplit
  simpa [finiteAverage] using hsplit

/-! ## Fixed-mask restriction and the unconditional slice bound -/

/-- Conditional expectation of `f` over the coordinates left live by one
fixed mask. -/
def fixedMaskAveragedFunction {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat)
    (mask base : Fin coordinateCount -> Bool) : Rat :=
  finiteAverage (fun uniform : Fin coordinateCount -> Bool =>
    f (maskedInput base mask uniform))

theorem fixedMaskAveragedFunction_eq_frozenFourierSum
    {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat)
    (mask base : Fin coordinateCount -> Bool) :
    fixedMaskAveragedFunction f mask base =
      ∑ support : Finset (Fin coordinateCount),
        coefficient f support * character support base *
          maskAllZeroIndicator support mask := by
  classical
  unfold fixedMaskAveragedFunction
  calc
    finiteAverage (fun uniform : Fin coordinateCount -> Bool =>
        f (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin coordinateCount -> Bool =>
        ∑ support : Finset (Fin coordinateCount),
          coefficient f support *
            character support (maskedInput base mask uniform)) := by
      apply finiteAverage_congr
      intro uniform
      exact (fourier_inversion f (maskedInput base mask uniform)).symm
    _ = ∑ support : Finset (Fin coordinateCount),
        finiteAverage (fun uniform : Fin coordinateCount -> Bool =>
          coefficient f support *
            character support (maskedInput base mask uniform)) := by
      simpa using finiteAverage_finset_sum
        (Finset.univ : Finset (Finset (Fin coordinateCount)))
        (fun support uniform => coefficient f support *
          character support (maskedInput base mask uniform))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro support hsupport
      rw [finiteAverage_const_mul]
      change coefficient f support *
          restrictedCharacterAverage support base mask = _
      rw [restrictedCharacterAverage_eq]
      ring

theorem coefficient_const_mul_character
    {coordinateCount : Nat} (constant : Rat)
    (support target : Finset (Fin coordinateCount)) :
    coefficient (fun input => constant * character support input) target =
      if target = support then constant else 0 := by
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : Fin coordinateCount -> Bool =>
        (constant * character support input) * character target input) =
      constant * finiteAverage (fun input : Fin coordinateCount -> Bool =>
        character support input * character target input) := by
      rw [← finiteAverage_const_mul]
      apply finiteAverage_congr
      intro input
      ring
    _ = _ := by
      rw [finiteAverage_character_mul_character]
      by_cases heq : target = support
      · simp [heq]
      · simp [heq, Ne.symm heq]

/-- Fourier coefficients of fixed-mask conditional expectation are exactly
the original coefficients whose supports are completely frozen. -/
theorem coefficient_fixedMaskAveragedFunction
    {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat)
    (mask : Fin coordinateCount -> Bool)
    (target : Finset (Fin coordinateCount)) :
    coefficient (fixedMaskAveragedFunction f mask) target =
      coefficient f target * maskAllZeroIndicator target mask := by
  classical
  have hfunction : fixedMaskAveragedFunction f mask =
      fun base => ∑ support : Finset (Fin coordinateCount),
        (coefficient f support * maskAllZeroIndicator support mask) *
          character support base := by
    funext base
    rw [fixedMaskAveragedFunction_eq_frozenFourierSum]
    apply Finset.sum_congr rfl
    intro support hsupport
    ring
  rw [hfunction]
  rw [FiniteUnambiguousFBDD.coefficient_fintype_sum]
  simp_rw [coefficient_const_mul_character]
  simp

theorem abs_fixedMaskAveragedFunction_le_one
    {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1)
    (mask base : Fin coordinateCount -> Bool) :
    |fixedMaskAveragedFunction f mask base| <= 1 := by
  have hcard :
      (0 : Rat) < (Fintype.card (Fin coordinateCount -> Bool) : Rat) := by
    exact_mod_cast Fintype.card_pos
  unfold fixedMaskAveragedFunction finiteAverage
  rw [abs_div, abs_of_pos hcard]
  apply (div_le_iff₀ hcard).mpr
  calc
    |∑ uniform : Fin coordinateCount -> Bool,
        f (maskedInput base mask uniform)| <=
      ∑ uniform : Fin coordinateCount -> Bool,
        |f (maskedInput base mask uniform)| :=
      Finset.abs_sum_le_sum_abs _ Finset.univ
    _ <= ∑ _uniform : Fin coordinateCount -> Bool, (1 : Rat) := by
      exact Finset.sum_le_sum fun uniform _ =>
        hbounded (maskedInput base mask uniform)
    _ = 1 * (Fintype.card (Fin coordinateCount -> Bool) : Rat) := by simp

/-- The fixed-mask dual slice is the all-false structured far correlation of
the bounded conditional-expectation function. -/
theorem structuredDualPairCorrelationAtMask_self_eq_fixedMaskAllFalseFar
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) :
    structuredDualPairCorrelationAtMask n m (2 * m) hn f f mask =
      highTailFarPairCorrelation
        (fixedMaskAveragedFunction f mask) (2 * m)
        (structuredIndependence m)
        (structuredUnbiasedPrimitive n m hn).generate allFalseMask := by
  rw [← structuredDualAliasPairCoefficientSum_self_eq_allFalseFar]
  unfold structuredDualPairCorrelationAtMask
    structuredDualAliasPairCoefficient
  apply Finset.sum_congr rfl
  intro pair hpair
  rw [coefficient_fixedMaskAveragedFunction,
    coefficient_fixedMaskAveragedFunction]
  rw [← maskAllZeroIndicator_mul_eq_union]
  ring

/-- Every fixed mask slice has absolute signed correlation at most `4` for a
pointwise-`1`-bounded function. -/
theorem abs_structuredDualPairCorrelationAtMask_self_le_four
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1)
    (mask : Fin (2 ^ n) -> Bool) :
    |structuredDualPairCorrelationAtMask n m (2 * m) hn f f mask| <= 4 := by
  rw [structuredDualPairCorrelationAtMask_self_eq_fixedMaskAllFalseFar]
  exact abs_structured_allFalse_highTailFarPairCorrelation_le_four
    n m hn (fixedMaskAveragedFunction f mask)
      (abs_fixedMaskAveragedFunction_le_one f hbounded mask)

/-- The concrete small-seed signed pair correlation: uniformly average the
surviving pair sum over all nonzero `((4m+1)n)`-bit coefficient seeds. -/
def structuredDualNonzeroSeedCrossCorrelation
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) : Rat :=
  nonzeroBitSeedAverage (structuredIndependence m * n)
    (fun seed : FiniteBitTape (structuredIndependence m * n) =>
      structuredDualPairCorrelationAtMask n m cutoff hn
        leftFunction rightFunction
        ((structuredDyadicPrimitive n m tailBits hn htail).generate seed))

/-- The conditional nonzero-seed signed correlation is exactly conditional
structured restriction energy minus the diagonal Fourier energy.  Each
diagonal support is weighted by its exact hyperplane survival probability,
not by a rank lower bound or a relaxed tail estimate. -/
theorem structuredDualNonzeroSeedCrossCorrelation_eq_conditionalSecondMoment_sub_hyperplaneDiagonal
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualNonzeroSeedCrossCorrelation
        n m tailBits (2 * m) hn htail f f =
      nonzeroBitSeedAverage (structuredIndependence m * n)
          (fun maskSeed : FiniteBitTape (structuredIndependence m * n) =>
            finiteAverage
              (fun baseSeed :
                  FiniteBitTape (structuredIndependence m * n) =>
                (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
                  FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
                    (maskedInput
                      ((structuredUnbiasedPrimitive n m hn).generate baseSeed)
                      ((structuredDyadicPrimitive n m tailBits hn htail).generate
                        maskSeed)
                      uniform))) ^ 2)) -
        ∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
          (coefficient f support) ^ 2 *
            hyperplaneSurvivalWeight
              (structuredIndependence m * n)
              (supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail support) := by
  classical
  have hpointwise
      (maskSeed : FiniteBitTape (structuredIndependence m * n)) :
      structuredDualPairCorrelationAtMask n m (2 * m) hn f f
          ((structuredDyadicPrimitive n m tailBits hn htail).generate
            maskSeed) =
        finiteAverage
            (fun baseSeed :
                FiniteBitTape (structuredIndependence m * n) =>
              (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
                FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
                  (maskedInput
                    ((structuredUnbiasedPrimitive n m hn).generate baseSeed)
                    ((structuredDyadicPrimitive n m tailBits hn htail).generate
                      maskSeed)
                    uniform))) ^ 2) -
          ∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
            (coefficient f support) ^ 2 *
              maskAllZeroIndicator support
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  maskSeed) := by
    have hsplit :=
      structured_fixedMask_highTail_secondMoment_eq_diagonal_add_pairCorrelation
        n m hn f
          ((structuredDyadicPrimitive n m tailBits hn htail).generate maskSeed)
    linarith
  unfold structuredDualNonzeroSeedCrossCorrelation
  calc
    nonzeroBitSeedAverage (structuredIndependence m * n)
        (fun seed : FiniteBitTape (structuredIndependence m * n) =>
          structuredDualPairCorrelationAtMask n m (2 * m) hn f f
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) =
      nonzeroBitSeedAverage (structuredIndependence m * n)
        (fun maskSeed : FiniteBitTape (structuredIndependence m * n) =>
          finiteAverage
              (fun baseSeed :
                  FiniteBitTape (structuredIndependence m * n) =>
                (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
                  FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
                    (maskedInput
                      ((structuredUnbiasedPrimitive n m hn).generate baseSeed)
                      ((structuredDyadicPrimitive n m tailBits hn htail).generate
                        maskSeed)
                      uniform))) ^ 2) -
            ∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
              (coefficient f support) ^ 2 *
                maskAllZeroIndicator support
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    maskSeed)) := by
        apply nonzeroBitSeedAverage_congr
        intro maskSeed hmaskSeed
        exact hpointwise maskSeed
    _ = nonzeroBitSeedAverage (structuredIndependence m * n)
          (fun maskSeed : FiniteBitTape (structuredIndependence m * n) =>
            finiteAverage
              (fun baseSeed :
                  FiniteBitTape (structuredIndependence m * n) =>
                (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
                  FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
                    (maskedInput
                      ((structuredUnbiasedPrimitive n m hn).generate baseSeed)
                      ((structuredDyadicPrimitive n m tailBits hn htail).generate
                        maskSeed)
                      uniform))) ^ 2)) -
        nonzeroBitSeedAverage (structuredIndependence m * n)
          (fun maskSeed : FiniteBitTape (structuredIndependence m * n) =>
            ∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
              (coefficient f support) ^ 2 *
                maskAllZeroIndicator support
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    maskSeed)) := by
        exact nonzeroBitSeedAverage_sub _ _ _
    _ = _ := by
      congr 1
      rw [nonzeroBitSeedAverage_finset_sum]
      apply Finset.sum_congr rfl
      intro support hsupport
      calc
        nonzeroBitSeedAverage (structuredIndependence m * n)
            (fun maskSeed : FiniteBitTape (structuredIndependence m * n) =>
              (coefficient f support) ^ 2 *
                maskAllZeroIndicator support
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    maskSeed)) =
          nonzeroBitSeedAverage (structuredIndependence m * n)
            (fun maskSeed : FiniteBitTape (structuredIndependence m * n) =>
              maskAllZeroIndicator support
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    maskSeed) *
                (coefficient f support) ^ 2) := by
            apply nonzeroBitSeedAverage_congr
            intro maskSeed hmaskSeed
            ring
        _ = nonzeroBitSeedAverage (structuredIndependence m * n)
              (fun maskSeed : FiniteBitTape (structuredIndependence m * n) =>
                maskAllZeroIndicator support
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    maskSeed)) *
              (coefficient f support) ^ 2 := by
            exact nonzeroBitSeedAverage_mul_const _ _ _
        _ = (coefficient f support) ^ 2 *
              hyperplaneSurvivalWeight
                (structuredIndependence m * n)
                (supportPrefixConstraintRank n (structuredIndependence m)
                  tailBits hn htail support) := by
            rw [structuredDyadicPrimitive_nonzeroSeed_maskSurvival_eq_hyperplaneWeight]
            ring

/-- The hyperplane-smoothed form is exactly the concrete conditional
nonzero-seed pair correlation. -/
theorem structuredDualHyperplaneSmoothedCrossForm_eq_nonzeroSeedCorrelation
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualHyperplaneSmoothedCrossForm
        n m tailBits cutoff hn htail leftFunction rightFunction =
      structuredDualNonzeroSeedCrossCorrelation
        n m tailBits cutoff hn htail leftFunction rightFunction := by
  classical
  unfold structuredDualHyperplaneSmoothedCrossForm
    structuredDualNonzeroSeedCrossCorrelation
    structuredDualPairCorrelationAtMask
  rw [nonzeroBitSeedAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro pair hpair
  rw [nonzeroBitSeedAverage_mul_const]
  rw [structuredDyadicPrimitive_nonzeroSeed_maskSurvival_eq_hyperplaneWeight]
  rfl

/-- Averaging the unconditional fixed-mask slice bound over the nonzero mask
seeds gives the universal signed cap `4`. -/
theorem structuredDualNonzeroSeedCrossCorrelation_le_four
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1) :
    structuredDualNonzeroSeedCrossCorrelation
        n m tailBits (2 * m) hn htail f f <= 4 := by
  unfold structuredDualNonzeroSeedCrossCorrelation
  apply nonzeroBitSeedAverage_le_of_pointwise
    (structuredIndependence m * n)
    (Nat.mul_pos (by unfold structuredIndependence; omega) hn)
  intro seed hseed
  exact (le_abs_self _).trans
    (abs_structuredDualPairCorrelationAtMask_self_le_four
      n m hn f hbounded
        ((structuredDyadicPrimitive n m tailBits hn htail).generate seed))

/-- Equivalently, the hyperplane-smoothed self-form has the same universal
upper cap.  This does not approach the much smaller sharp conditional budget
needed below. -/
theorem structuredDualHyperplaneSmoothedCrossForm_self_le_four
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1) :
    structuredDualHyperplaneSmoothedCrossForm
        n m tailBits (2 * m) hn htail f f <= 4 := by
  rw [structuredDualHyperplaneSmoothedCrossForm_eq_nonzeroSeedCorrelation]
  exact structuredDualNonzeroSeedCrossCorrelation_le_four
    n m tailBits hn htail f hbounded

/-! ## Sharp conditional-seed budgets -/

/-- Exact conditional-budget reformulation of the weighted dual-far bound.
The right side retains the actual signed terminal form, so no terminal
relaxation occurs in this equivalence. -/
theorem structuredDualNonzeroSeedCrossCorrelation_le_exactBudget_iff
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) (budget : Rat) :
    structuredDualNonzeroSeedCrossCorrelation
        n m tailBits cutoff hn htail f f <=
      (budget -
          dyadicRankWeight (structuredIndependence m * n) *
            structuredDualRankAtMostCrossForm
              n m tailBits cutoff hn htail f f
                (structuredIndependence m * n)) /
        (1 - dyadicRankWeight (structuredIndependence m * n)) ↔
      structuredRankWeightedDualFarPairCorrelation
          n m tailBits cutoff hn htail f <= budget := by
  rw [structuredRankWeightedDualFarPairCorrelation_eq_hyperplane_add_terminal]
  rw [structuredDualHyperplaneSmoothedCrossForm_eq_nonzeroSeedCorrelation]
  have hfactorPos :
      0 < 1 - dyadicRankWeight (structuredIndependence m * n) :=
    one_sub_dyadicRankWeight_pos_of_pos
      (Nat.mul_pos (by unfold structuredIndependence; omega) hn)
  constructor
  · intro h
    have hmul := (le_div_iff₀ hfactorPos).mp h
    linarith
  · intro h
    apply (le_div_iff₀ hfactorPos).mpr
    linarith

/-- Replacing the actual terminal form by its unconditional upper cap `4`
gives a slightly stronger but terminal-independent conditional-seed budget. -/
theorem structuredDualFarPairCorrelation_le_budget_of_nonzeroSeedFourBudget
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) (budget : Rat)
    (hbounded : forall input, |f input| <= 1)
    (hnonzero :
      structuredDualNonzeroSeedCrossCorrelation
          n m tailBits cutoff hn htail f f <=
        (budget - 4 *
            dyadicRankWeight (structuredIndependence m * n)) /
          (1 - dyadicRankWeight (structuredIndependence m * n)))
    (hcutoff : cutoff = 2 * m) :
    structuredDualFarPairCorrelation n m tailBits cutoff hn htail f <=
      budget := by
  subst cutoff
  let upperRank := structuredIndependence m * n
  let terminal := structuredDualRankAtMostCrossForm
    n m tailBits (2 * m) hn htail f f upperRank
  have hfactorPos : 0 < 1 - dyadicRankWeight upperRank :=
    one_sub_dyadicRankWeight_pos_of_pos
      (Nat.mul_pos (by unfold structuredIndependence; omega) hn)
  have hterminal : terminal <= 4 := by
    dsimp [terminal, upperRank]
    exact structuredDualRankAtMostCrossForm_terminal_le_four
      n m tailBits hn htail f hbounded
  have hweightNonneg : 0 <= dyadicRankWeight upperRank :=
    dyadicRankWeight_nonneg upperRank
  have hmul := (le_div_iff₀ hfactorPos).mp hnonzero
  have hexact :
      structuredDualNonzeroSeedCrossCorrelation
          n m tailBits (2 * m) hn htail f f <=
        (budget - dyadicRankWeight upperRank * terminal) /
          (1 - dyadicRankWeight upperRank) := by
    apply (le_div_iff₀ hfactorPos).mpr
    have hterminalWeighted :
        dyadicRankWeight upperRank * terminal <=
          dyadicRankWeight upperRank * 4 :=
      mul_le_mul_of_nonneg_left hterminal hweightNonneg
    dsimp [upperRank, terminal] at hmul ⊢
    linarith
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  exact (structuredDualNonzeroSeedCrossCorrelation_le_exactBudget_iff
    n m tailBits (2 * m) hn htail f budget).mp hexact

/-- The preceding theorem at the exact `DualFarBound` budget.  This is a
concrete sufficient target after the unconditional terminal-`4` relaxation;
the actual-terminal equivalence above is the sharp target. -/
theorem structuredDualFarPairCorrelation_le_dualFarBudget_of_nonzeroSeedFourBudget
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1)
    (hnonzero :
      structuredDualNonzeroSeedCrossCorrelation
          n m tailBits (2 * m) hn htail f f <=
        (((1 - 1 / (2 : Rat) ^ tailBits) *
              (1 / (2 : Rat) ^ tailBits) ^ (2 * m)) -
            4 * dyadicRankWeight (structuredIndependence m * n)) /
          (1 - dyadicRankWeight (structuredIndependence m * n))) :
    structuredDualFarPairCorrelation n m tailBits (2 * m) hn htail f <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
        (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  exact structuredDualFarPairCorrelation_le_budget_of_nonzeroSeedFourBudget
    n m tailBits (2 * m) hn htail f _ hbounded hnonzero rfl

/-! ## Exact mandatory-selector characterizations and capstones -/

/-- For one actual affine prefix, `DualFarBound` is exactly the displayed
conditional nonzero-seed inequality with the actual signed terminal form.
This theorem introduces no separately named mathematical premise. -/
theorem dualFarBound_iff_mandatorySelectorNonzeroSeedExactBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let f :=
      (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
    DualFarBound machine n T b m tailBits hn htail rounds ↔
      structuredDualNonzeroSeedCrossCorrelation
          n m tailBits (2 * m) hn htail f f <=
        (((1 - 1 / (2 : Rat) ^ tailBits) *
              (1 / (2 : Rat) ^ tailBits) ^ (2 * m)) -
            dyadicRankWeight (structuredIndependence m * n) *
              structuredDualRankAtMostCrossForm
                n m tailBits (2 * m) hn htail f f
                  (structuredIndependence m * n)) /
          (1 - dyadicRankWeight (structuredIndependence m * n)) := by
  dsimp only
  unfold DualFarBound
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  exact (structuredDualNonzeroSeedCrossCorrelation_le_exactBudget_iff
    n m tailBits (2 * m) hn htail
      (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
      ((1 - 1 / (2 : Rat) ^ tailBits) *
        (1 / (2 : Rat) ^ tailBits) ^ (2 * m))).symm

/-- With positive block size, the same exact characterization is written
directly for the affine-prefixed cached one-tape run predicate.  This is the
transition-semantic form of the remaining numerical inequality. -/
theorem dualFarBound_iff_cachedRunNonzeroSeedExactBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let f := affinePrefixedCachedRunAcceptanceIndicator machine n T rounds
    DualFarBound machine n T b m tailBits hn htail rounds ↔
      structuredDualNonzeroSeedCrossCorrelation
          n m tailBits (2 * m) hn htail f f <=
        (((1 - 1 / (2 : Rat) ^ tailBits) *
              (1 / (2 : Rat) ^ tailBits) ^ (2 * m)) -
            dyadicRankWeight (structuredIndependence m * n) *
              structuredDualRankAtMostCrossForm
                n m tailBits (2 * m) hn htail f f
                  (structuredIndependence m * n)) /
          (1 - dyadicRankWeight (structuredIndependence m * n)) := by
  dsimp only
  have hf :
      (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator =
        affinePrefixedCachedRunAcceptanceIndicator machine n T rounds :=
    funext fun input =>
      prefixedMandatoryCanonicalSelector_ratAcceptanceIndicator_eq_cachedRun
        machine n T b hb rounds input
  simpa only [hf] using
    (dualFarBound_iff_mandatorySelectorNonzeroSeedExactBudget
      machine n T b m tailBits hn htail rounds)

/-- A concrete sufficient selector-pair lemma using only the unconditional
terminal cap `4`.  Its premise is the explicit normalized nonzero-seed sum,
not a separately named open proposition. -/
theorem dualFarBound_of_mandatorySelectorNonzeroSeedFourBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hcorrelation :
      let f :=
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
      structuredDualNonzeroSeedCrossCorrelation
          n m tailBits (2 * m) hn htail f f <=
        (((1 - 1 / (2 : Rat) ^ tailBits) *
              (1 / (2 : Rat) ^ tailBits) ^ (2 * m)) -
            4 * dyadicRankWeight (structuredIndependence m * n)) /
          (1 - dyadicRankWeight (structuredIndependence m * n))) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  unfold DualFarBound
  exact structuredDualFarPairCorrelation_le_dualFarBudget_of_nonzeroSeedFourBudget
    n m tailBits hn htail B.ratAcceptanceIndicator
      (by
        intro input
        classical
        by_cases haccepts : B.Accepts input <;>
          simp [FiniteUnambiguousFBDD.ratAcceptanceIndicator, haccepts])
      hcorrelation

/-- Exact generated-prefix characterization, still written as the concrete
conditional inequality rather than a newly named premise. -/
theorem generatedPrefixDualFarBound_iff_mandatorySelectorNonzeroSeedExactBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n) :
    GeneratedPrefixDualFarBound machine n T b m tailBits hn htail ↔
      forall (r : Nat)
        (oldSeeds : Seeds
          (FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n)) r),
        let rounds := roundsOfSeeds
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate
          r oldSeeds
        let f :=
          (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
        structuredDualNonzeroSeedCrossCorrelation
            n m tailBits (2 * m) hn htail f f <=
          (((1 - 1 / (2 : Rat) ^ tailBits) *
                (1 / (2 : Rat) ^ tailBits) ^ (2 * m)) -
              dyadicRankWeight (structuredIndependence m * n) *
                structuredDualRankAtMostCrossForm
                  n m tailBits (2 * m) hn htail f f
                    (structuredIndependence m * n)) /
            (1 - dyadicRankWeight (structuredIndependence m * n)) := by
  constructor
  · intro hfar r oldSeeds
    exact (dualFarBound_iff_mandatorySelectorNonzeroSeedExactBudget
      machine n T b m tailBits hn htail _).mp (hfar r oldSeeds)
  · intro hcorrelation r oldSeeds
    exact (dualFarBound_iff_mandatorySelectorNonzeroSeedExactBudget
      machine n T b m tailBits hn htail _).mpr
        (hcorrelation r oldSeeds)

/-- The terminal-`4` conditional budget at every generated prefix implies
the existing hybrid-facing generated-prefix interface. -/
theorem generatedPrefixDualFarBound_of_mandatorySelectorNonzeroSeedFourBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (hcorrelation : forall (r : Nat)
      (oldSeeds : Seeds
        (FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n)) r),
      let rounds := roundsOfSeeds
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate
        r oldSeeds
      let f :=
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
      structuredDualNonzeroSeedCrossCorrelation
          n m tailBits (2 * m) hn htail f f <=
        (((1 - 1 / (2 : Rat) ^ tailBits) *
              (1 / (2 : Rat) ^ tailBits) ^ (2 * m)) -
            4 * dyadicRankWeight (structuredIndependence m * n)) /
          (1 - dyadicRankWeight (structuredIndependence m * n))) :
    GeneratedPrefixDualFarBound machine n T b m tailBits hn htail := by
  intro r oldSeeds
  exact dualFarBound_of_mandatorySelectorNonzeroSeedFourBudget
    machine n T b m tailBits hn htail _ (hcorrelation r oldSeeds)

end FiniteStructuredDualNonzeroSeedCorrelation
end

end OneTapeMagnification
end Frontier
end Pnp4
