import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorSyndromeLeakageIdentity
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A relative syndrome-frame bridge for the mandatory selector

The exact whole-selector leakage identity leaves one quantitative question.
This module records a sufficient relative frame condition and proves its
consequence; it does not assert that the condition follows from one-tape
semantics.

Writing `E` for the mask-averaged squared syndrome-fiber projection, `D` for
the corresponding Fourier diagonal, and `p = 2^(-tailBits)`, the condition is

`p * E <= D`.

Together with the existing diagonal estimate `D <= p^(2*m+1)`, it gives

`E - D <= (1-p) * p^(2*m)`,

which is exactly the signed selector-pair budget.  A fiberwise Bessel bound
with coherence at most `1/p` is also proved sufficient for the frame
condition.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanPerVertexRestrictionBound
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredRankWeightedDualCorrelation
open FiniteAffineRestrictionHybrid
open FiniteSignedReverseLCPSiblingDualRank
open FiniteStructuredDualRankThresholdBridge
open FiniteStructuredDualSyndromeFiberBlocks
open MandatoryCanonicalSelectorPairCorrelation

namespace MandatoryCanonicalSelectorSyndromeFrameBridge

/-! ## Generic finite algebra -/

/-- The exact scalar calculation behind the frame bridge. -/
theorem sub_le_one_sub_mul_pow_of_frame_and_diagonal
    (m : Nat) (p E D : Rat)
    (hp0 : 0 < p) (hp1 : p <= 1)
    (hframe : p * E <= D)
    (hdiagonal : D <= p ^ (2 * m + 1)) :
    E - D <= (1 - p) * p ^ (2 * m) := by
  have hone : 0 <= 1 - p := sub_nonneg.mpr hp1
  have hscaledDiagonal :
      (1 - p) * D <= (1 - p) * p ^ (2 * m + 1) :=
    mul_le_mul_of_nonneg_left hdiagonal hone
  have hscaled :
      p * (E - D) <= (1 - p) * p ^ (2 * m + 1) := by
    nlinarith
  have hpow : p ^ (2 * m + 1) = p ^ (2 * m) * p := by
    rw [pow_succ]
  rw [hpow] at hscaled
  nlinarith

/-- A generic fiberwise Bessel estimate implies the summed frame estimate.
The statement isolates the only use of the all-ones direction inside each
fiber. -/
theorem finite_fiberwise_bessel_implies_frame
    {Index Label : Type*} [Fintype Label]
    [DecidableEq Index] [DecidableEq Label]
    (indices : Finset Index) (label : Index -> Label)
    (coefficient : Index -> Rat) (p : Rat)
    (hfiber : forall fiber : Label,
      p * (Finset.sum indices (fun index =>
        if label index = fiber then coefficient index else 0)) ^ 2 <=
      Finset.sum indices (fun index =>
        if label index = fiber then (coefficient index) ^ 2 else 0)) :
    p * (Finset.univ.sum (fun fiber : Label =>
      (Finset.sum indices (fun index =>
        if label index = fiber then coefficient index else 0)) ^ 2)) <=
      Finset.sum indices (fun index => (coefficient index) ^ 2) := by
  classical
  calc
    p * (Finset.univ.sum (fun fiber : Label =>
        (Finset.sum indices (fun index =>
          if label index = fiber then coefficient index else 0)) ^ 2)) =
      Finset.univ.sum (fun fiber : Label =>
        p * (Finset.sum indices (fun index =>
          if label index = fiber then coefficient index else 0)) ^ 2) := by
            rw [Finset.mul_sum]
    _ <= Finset.univ.sum (fun fiber : Label =>
        Finset.sum indices (fun index =>
          if label index = fiber then (coefficient index) ^ 2 else 0)) := by
            exact Finset.sum_le_sum fun fiber _ => hfiber fiber
    _ = Finset.sum indices (fun index => (coefficient index) ^ 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro index _hindex
      simp

/-! ## Structured-mask energy and diagonal -/

/-- Mask-averaged squared projection onto the high-degree all-ones syndrome
directions. -/
def structuredSyndromeEnergyAverage
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) : Rat :=
  finiteAverage
    (fun maskSeed : Fin (structuredIndependence m * n) -> Bool =>
      let mask :=
        (structuredDyadicPrimitive n m tailBits hn htail).generate maskSeed
      Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
        (structuredSyndromeFiberCoefficientSum n m cutoff hn
          f mask syndrome) ^ 2))

/-- The same mask average applied to the high-degree Fourier diagonal. -/
def structuredMaskedHighDiagonalAverage
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) : Rat :=
  finiteAverage
    (fun maskSeed : Fin (structuredIndependence m * n) -> Bool =>
      structuredMaskedHighDiagonalCrossTerm n cutoff f f
        ((structuredDyadicPrimitive n m tailBits hn htail).generate maskSeed))

/-- Exact expansion of the averaged diagonal in the form consumed by the
bounded-independence diagonal theorem. -/
theorem structuredMaskedHighDiagonalAverage_eq_sum
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredMaskedHighDiagonalAverage n m tailBits cutoff hn htail f =
      Finset.sum (highDegreeSupports (2 ^ n) cutoff) (fun support =>
        (coefficient f support) ^ 2 *
          finiteAverage
            (fun maskSeed : Fin (structuredIndependence m * n) -> Bool =>
              maskAllZeroIndicator support
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  maskSeed))) := by
  classical
  unfold structuredMaskedHighDiagonalAverage
  simp_rw [structuredMaskedHighDiagonalCrossTerm_eq]
  rw [finiteAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro support _hsupport
  calc
    (finiteAverage fun maskSeed =>
        maskAllZeroIndicator support
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                maskSeed) *
            coefficient f support * coefficient f support) =
      finiteAverage (fun maskSeed =>
        (coefficient f support) ^ 2 *
          maskAllZeroIndicator support
            ((structuredDyadicPrimitive n m tailBits hn htail).generate
              maskSeed)) := by
                apply finiteAverage_congr
                intro maskSeed
                ring
    _ = (coefficient f support) ^ 2 *
        finiteAverage
          (fun maskSeed : Fin (structuredIndependence m * n) -> Bool =>
            maskAllZeroIndicator support
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                maskSeed)) := by
                  rw [finiteAverage_const_mul]

/-- The exact rank-weighted distinct-alias form is energy minus diagonal. -/
theorem structuredDualRankDistinctCrossForm_eq_energy_sub_diagonal
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail f f =
      structuredSyndromeEnergyAverage n m tailBits cutoff hn htail f -
        structuredMaskedHighDiagonalAverage
          n m tailBits cutoff hn htail f := by
  classical
  rw [structuredDualRankDistinctCrossForm_eq_finiteAverage_syndromeFiberBlocks]
  unfold structuredSyndromeEnergyAverage structuredMaskedHighDiagonalAverage
  simp only [pow_two]
  rw [FiniteBooleanOneRoundFoolingBound.finiteAverage_sub]

/-- The relative frame inequality.  This is a quantitative source condition,
not an unconditional property of selectors or one-tape machines. -/
def StructuredSyndromeFrameBound
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) : Prop :=
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  p * structuredSyndromeEnergyAverage n m tailBits cutoff hn htail f <=
    structuredMaskedHighDiagonalAverage n m tailBits cutoff hn htail f

/-- A pointwise syndrome-fiber coherence bound of `1/p` implies the averaged
frame condition. -/
theorem structuredSyndromeFrameBound_of_fiberwise
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hfiber :
      let p : Rat := 1 / (2 : Rat) ^ tailBits
      forall (maskSeed : Fin (structuredIndependence m * n) -> Bool)
        (syndrome : StructuredDualPowerSyndrome n m),
        let mask :=
          (structuredDyadicPrimitive n m tailBits hn htail).generate maskSeed
        p * (structuredSyndromeFiberCoefficientSum n m cutoff hn
          f mask syndrome) ^ 2 <=
          Finset.sum (highDegreeSupports (2 ^ n) cutoff) (fun support =>
            if structuredDualPowerSyndrome n m hn support = syndrome then
              (structuredMaskedCoefficient f mask support) ^ 2
            else 0)) :
    StructuredSyndromeFrameBound n m tailBits cutoff hn htail f := by
  classical
  dsimp only at hfiber
  unfold StructuredSyndromeFrameBound
  dsimp only
  unfold structuredSyndromeEnergyAverage structuredMaskedHighDiagonalAverage
  rw [<- finiteAverage_const_mul]
  apply finiteAverage_mono
  intro maskSeed
  let mask :=
    (structuredDyadicPrimitive n m tailBits hn htail).generate maskSeed
  have hpoint := finite_fiberwise_bessel_implies_frame
    (indices := highDegreeSupports (2 ^ n) cutoff)
    (label := structuredDualPowerSyndrome n m hn)
    (coefficient := structuredMaskedCoefficient f mask)
    (p := 1 / (2 : Rat) ^ tailBits)
    (fun syndrome => hfiber maskSeed syndrome)
  simpa [structuredSyndromeFiberCoefficientSum,
    structuredMaskedHighDiagonalCrossTerm, pow_two] using hpoint

/-! ## Correlation endpoint -/

/-- The relative frame condition and the standard diagonal estimate imply
the desired rank-weighted distinct-alias budget for any bounded function. -/
theorem structuredDualRankDistinctCrossForm_le_of_syndromeFrameBound
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1)
    (hframe : StructuredSyndromeFrameBound
      n m tailBits (2 * m) hn htail f) :
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    structuredDualRankDistinctCrossForm
        n m tailBits (2 * m) hn htail f f <=
      (1 - p) * p ^ (2 * m) := by
  dsimp only
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let E := structuredSyndromeEnergyAverage
    n m tailBits (2 * m) hn htail f
  let D := structuredMaskedHighDiagonalAverage
    n m tailBits (2 * m) hn htail f
  have hp0 : 0 < p := by
    dsimp [p]
    positivity
  have hp1 : p <= 1 := by
    have hden0 : (0 : Rat) < (2 : Rat) ^ tailBits := by positivity
    have hden1 : (1 : Rat) <= (2 : Rat) ^ tailBits :=
      one_le_pow₀ (by norm_num : (1 : Rat) <= 2)
    dsimp [p]
    rw [div_le_iff₀ hden0]
    simpa using hden1
  have hcutoff : 2 * m + 1 <= structuredIndependence m := by
    unfold structuredIndependence
    omega
  have hdiagSum :
      Finset.sum (highDegreeSupports (2 ^ n) (2 * m)) (fun support =>
        (coefficient f support) ^ 2 *
          finiteAverage
            (fun maskSeed : Fin (structuredIndependence m * n) -> Bool =>
              maskAllZeroIndicator support
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  maskSeed))) <= p ^ (2 * m + 1) := by
    exact highTail_diagonalEnergy_le_pow_succ
      f (structuredDyadicPrimitive n m tailBits hn htail).generate p
        (le_of_lt hp0) hcutoff
        (structuredDyadicPrimitive_patternFalseBiased
          n m tailBits hn htail)
        hbounded
  have hdiagonal : D <= p ^ (2 * m + 1) := by
    dsimp only [D]
    rw [structuredMaskedHighDiagonalAverage_eq_sum]
    exact hdiagSum
  have hframe' : p * E <= D := by
    simpa [StructuredSyndromeFrameBound, p, E, D] using hframe
  have hscalar := sub_le_one_sub_mul_pow_of_frame_and_diagonal
    m p E D hp0 hp1 hframe' hdiagonal
  rw [structuredDualRankDistinctCrossForm_eq_energy_sub_diagonal]
  exact hscalar

/-- Machine-specific source condition on the actual affine-prefixed mandatory
selector.  No theorem below claims this proposition automatically holds. -/
def PrefixedMandatoryCanonicalSelectorSyndromeFrameBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Prop :=
  StructuredSyndromeFrameBound n m tailBits (2 * m) hn htail
    (FiniteUnambiguousFBDD.ratAcceptanceIndicator
      (prefixedMandatoryCanonicalSelector machine n T b rounds))

/-- The machine-specific syndrome-frame source implies the exact existing
`DualFarBound` endpoint. -/
theorem dualFarBound_of_prefixedMandatoryCanonicalSelectorSyndromeFrameBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hframe : PrefixedMandatoryCanonicalSelectorSyndromeFrameBound
      machine n T b m tailBits hn htail rounds) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  let f := (prefixedMandatoryCanonicalSelector
    machine n T b rounds).ratAcceptanceIndicator
  have hbounded : forall input, |f input| <= 1 := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have hcross :=
    structuredDualRankDistinctCrossForm_le_of_syndromeFrameBound
      n m tailBits hn htail f hbounded
        (by
          simpa [PrefixedMandatoryCanonicalSelectorSyndromeFrameBound, f]
            using hframe)
  dsimp only at hcross
  unfold DualFarBound
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  rw [<- structuredDualRankDistinctCrossForm_self_eq_rankWeightedDualFar]
  exact hcross

/-- Hybrid-facing frame source: only prefixes generated by old seeds are
quantified, exactly as in `GeneratedPrefixDualFarBound`. -/
def GeneratedPrefixSyndromeFrameBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n) : Prop :=
  forall (r : Nat)
    (oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r),
    PrefixedMandatoryCanonicalSelectorSyndromeFrameBound
      machine n T b m tailBits hn htail
        (roundsOfSeeds
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate
          r oldSeeds)

/-- Finite-round hybrid-facing frame source. -/
def GeneratedPrefixSyndromeFrameBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) : Prop :=
  forall (r : Nat), r < L ->
    forall oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      PrefixedMandatoryCanonicalSelectorSyndromeFrameBound
        machine n T b m tailBits hn htail
          (roundsOfSeeds
            (structuredUnbiasedPrimitive n m hn).generate
            (structuredDyadicPrimitive n m tailBits hn htail).generate
            r oldSeeds)

/-- The generated-prefix frame source implies the existing generated-prefix
correlation interface. -/
theorem generatedPrefixDualFarBound_of_generatedPrefixSyndromeFrameBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (hframe : GeneratedPrefixSyndromeFrameBound
      machine n T b m tailBits hn htail) :
    GeneratedPrefixDualFarBound machine n T b m tailBits hn htail := by
  intro r oldSeeds
  exact dualFarBound_of_prefixedMandatoryCanonicalSelectorSyndromeFrameBound
    machine n T b m tailBits hn htail _ (hframe r oldSeeds)

/-- The finite-prefix frame source implies the exact finite-prefix
correlation interface used by a bounded-round hybrid. -/
theorem generatedPrefixDualFarBoundUpTo_of_generatedPrefixSyndromeFrameBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (hframe : GeneratedPrefixSyndromeFrameBoundUpTo
      machine n T b m tailBits L hn htail) :
    GeneratedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail := by
  intro r hr oldSeeds
  exact dualFarBound_of_prefixedMandatoryCanonicalSelectorSyndromeFrameBound
    machine n T b m tailBits hn htail _ (hframe r hr oldSeeds)

end MandatoryCanonicalSelectorSyndromeFrameBridge
end
end OneTapeMagnification
end Frontier
end Pnp4
