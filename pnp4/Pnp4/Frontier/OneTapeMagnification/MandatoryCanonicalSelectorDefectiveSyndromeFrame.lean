import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorSyndromeFrameBridge
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorAbsoluteSyndromeEnergy
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Good/bad certificates for selector syndrome energy

The relative syndrome-frame condition can fail on coherent fibers even when
their absolute contribution is tiny.  This file records sufficient
``good/bad'' certificates which retain that distinction.

For a fixed mask the complete high-syndrome energy is at most `4`.  For a
Boolean-valued function there is a sharper mass-weighted envelope: it is at
most twice the conditional mass seen by the structured base source plus
twice the uniform mass.  A good mask may satisfy the relative frame bound,
while bad masks are charged to either envelope.  The resulting charge is
compared with the *actual* unused diagonal budget.

These are sufficient source conditions.  In particular, no theorem here
asserts that one-tape semantics makes the bad-mask charge small.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanMaskedProductFactorization
open FiniteBooleanPerVertexRestrictionBound
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredFullFieldCorrelation
open FiniteStructuredDualNonzeroSeedCorrelation
open FiniteStructuredDualSyndromeFiberBlocks
open FiniteStructuredDualBlockProductSyndromeTransform
open MandatoryCanonicalSelectorPairCorrelation
open MandatoryCanonicalSelectorResidualMass
open MandatoryCanonicalSelectorAbsoluteSyndromeEnergy
open MandatoryCanonicalSelectorSyndromeFrameBridge

namespace MandatoryCanonicalSelectorDefectiveSyndromeFrame

/-! ## A universal fixed-mask envelope -/

/-- Freezing a mask and then taking the structured high transform is exactly
the ordinary high Fourier tail of the fixed-mask conditional expectation. -/
theorem structuredMaskedHighDegreeTransform_eq_fixedMaskHighTail
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool)
    (seed : Fin (structuredIndependence m * n) -> Bool) :
    structuredMaskedHighDegreeTransform n m cutoff hn f mask seed =
      FiniteUnambiguousFBDD.ratHighDegreeFourierTail
        (fixedMaskAveragedFunction f mask) cutoff
        ((structuredUnbiasedPrimitive n m hn).generate seed) := by
  classical
  rw [ratHighDegreeFourierTail_eq_sum_highDegreeSupports]
  unfold structuredMaskedHighDegreeTransform structuredMaskedCoefficient
  apply Finset.sum_congr rfl
  intro support _hsupport
  rw [coefficient_fixedMaskAveragedFunction]
  ring

/-- The fixed-mask syndrome energy of a bounded function never exceeds four.
This is the cap used by the density-only bad-mask certificate below. -/
theorem fixedMask_syndromeFiberEnergy_le_four
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1)
    (mask : Fin (2 ^ n) -> Bool) :
    (Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
      (structuredSyndromeFiberCoefficientSum n m (2 * m) hn
        f mask syndrome) ^ 2)) <= 4 := by
  rw [show (Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
      (structuredSyndromeFiberCoefficientSum n m (2 * m) hn
        f mask syndrome) ^ 2)) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (structuredMaskedHighDegreeTransform n m (2 * m) hn
            f mask seed) ^ 2) by
    simpa only [pow_two] using
      (syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
        n m (2 * m) hn f f mask)]
  simp_rw [structuredMaskedHighDegreeTransform_eq_fixedMaskHighTail]
  exact DPTWStructuredFullFieldCorrelation.structured_unmaskedHighTail_secondMoment_le_four
    n m hn (fixedMaskAveragedFunction f mask)
      (abs_fixedMaskAveragedFunction_le_one f hbounded mask)

/-- Averaging the fixed-mask conditional expectation over a uniform base
recovers the original uniform mean. -/
theorem finiteAverage_fixedMaskAveragedFunction_eq
    {coordinateCount : Nat}
    (f : (Fin coordinateCount -> Bool) -> Rat)
    (mask : Fin coordinateCount -> Bool) :
    finiteAverage (fixedMaskAveragedFunction f mask) = finiteAverage f := by
  calc
    finiteAverage (fixedMaskAveragedFunction f mask) =
        coefficient (fixedMaskAveragedFunction f mask) ∅ := by
      rw [FiniteBooleanMaskedProductFactorization.coefficient_empty_eq_finiteAverage]
    _ = coefficient f ∅ * maskAllZeroIndicator ∅ mask := by
      rw [coefficient_fixedMaskAveragedFunction]
    _ = finiteAverage f := by
      rw [FiniteBooleanMaskedProductFactorization.coefficient_empty_eq_finiteAverage]
      simp [maskAllZeroIndicator]

/-- A mass-weighted version of the fixed-mask cap.  For a `[0,1]`-valued
function, coherent high-tail spikes are charged to the conditional mass seen
by the structured base source and to the original uniform mass.  This can be
much smaller than the constant `4` envelope. -/
theorem fixedMask_syndromeFiberEnergy_le_two_mul_structuredMass_add_uniformMass
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hunit : forall input, 0 <= f input ∧ f input <= 1)
    (mask : Fin (2 ^ n) -> Bool) :
    (Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
      (structuredSyndromeFiberCoefficientSum n m (2 * m) hn
        f mask syndrome) ^ 2)) <=
      2 * finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          fixedMaskAveragedFunction f mask
            ((structuredUnbiasedPrimitive n m hn).generate seed)) +
      2 * finiteAverage f := by
  let g := fixedMaskAveragedFunction f mask
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let low := ratLowDegreeFourierPart g (2 * m)
  have hgunit : forall input, 0 <= g input ∧ g input <= 1 := by
    intro input
    dsimp only [g]
    constructor
    · unfold fixedMaskAveragedFunction
      exact finiteAverage_nonneg fun uniform =>
        (hunit (maskedInput input mask uniform)).1
    · calc
        fixedMaskAveragedFunction f mask input <=
            finiteAverage (fun _uniform : Fin (2 ^ n) -> Bool => (1 : Rat)) := by
          unfold fixedMaskAveragedFunction
          apply finiteAverage_mono
          intro uniform
          exact (hunit (maskedInput input mask uniform)).2
        _ = 1 := by simp [finiteAverage]
  have hlowExact :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            (low (D seed)) ^ 2) =
        Finset.sum (lowDegreeSupports (2 ^ n) (2 * m))
          (fun support => (coefficient g support) ^ 2) := by
    simpa only using
      (lowDegreeFourierPart_secondMoment_eq_energy
        (q := structuredIndependence m) g D
        (by unfold structuredIndependence; omega)
        (structuredUnbiasedPrimitive_patternUnbiased n m hn))
  have hlow :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            (low (D seed)) ^ 2) <= finiteAverage f := by
    rw [hlowExact]
    calc
      Finset.sum (lowDegreeSupports (2 ^ n) (2 * m))
          (fun support => (coefficient g support) ^ 2) <=
          finiteAverage (fun input => (g input) ^ 2) :=
        bessel g (lowDegreeSupports (2 ^ n) (2 * m))
      _ <= finiteAverage g := by
        apply finiteAverage_mono
        intro input
        nlinarith [hgunit input]
      _ = finiteAverage f := by
        exact finiteAverage_fixedMaskAveragedFunction_eq f mask
  have hbase :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) -> Bool =>
            (g (D seed)) ^ 2) <=
        finiteAverage (fun seed => g (D seed)) := by
    apply finiteAverage_mono
    intro seed
    nlinarith [hgunit (D seed)]
  rw [show (Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
      (structuredSyndromeFiberCoefficientSum n m (2 * m) hn
        f mask syndrome) ^ 2)) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          (structuredMaskedHighDegreeTransform n m (2 * m) hn
            f mask seed) ^ 2) by
    simpa only [pow_two] using
      (syndromeFiberInnerProduct_eq_finiteAverage_highTransforms
        n m (2 * m) hn f f mask)]
  simp_rw [structuredMaskedHighDegreeTransform_eq_fixedMaskHighTail]
  change finiteAverage (fun seed =>
      (FiniteUnambiguousFBDD.ratHighDegreeFourierTail
        g (2 * m) (D seed)) ^ 2) <= _
  calc
    finiteAverage (fun seed =>
        (FiniteUnambiguousFBDD.ratHighDegreeFourierTail
          g (2 * m) (D seed)) ^ 2) <=
      finiteAverage (fun seed =>
        2 * (g (D seed)) ^ 2 + 2 * (low (D seed)) ^ 2) := by
          apply finiteAverage_mono
          intro seed
          rw [ratHighDegreeFourierTail_eq_sub_lowDegreePart]
          dsimp only [low]
          nlinarith [sq_nonneg (g (D seed) +
            ratLowDegreeFourierPart g (2 * m) (D seed))]
    _ = 2 * finiteAverage (fun seed => (g (D seed)) ^ 2) +
        2 * finiteAverage (fun seed => (low (D seed)) ^ 2) := by
      rw [finiteAverage_add_local, finiteAverage_const_mul,
        finiteAverage_const_mul]
    _ <= 2 * finiteAverage (fun seed => g (D seed)) +
        2 * finiteAverage f := by linarith
    _ = _ := by rfl

/-! ## Generic good/bad averaging -/

/-- Normalized density of an explicitly listed exceptional set. -/
def badSeedDensity {Seed : Type*} [Fintype Seed]
    [DecidableEq Seed] (bad : Finset Seed) : Rat :=
  finiteAverage (fun seed : Seed => if seed ∈ bad then 1 else 0)

/-- The part of an envelope carried by the exceptional set. -/
def badEnvelopeAverage {Seed : Type*} [Fintype Seed]
    [DecidableEq Seed] (bad : Finset Seed)
    (envelope : Seed -> Rat) : Rat :=
  finiteAverage (fun seed : Seed =>
    if seed ∈ bad then envelope seed else 0)

/-- Abstract defective-frame calculation.  Relative frame control is needed
only off `bad`; on `bad`, any proved pointwise envelope may be charged against
the unused global budget. -/
theorem finiteAverage_energy_le_of_good_bad_envelope
    {Seed : Type*} [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]
    (bad : Finset Seed) (energy diagonal envelope : Seed -> Rat)
    (p target : Rat)
    (hp : 0 < p)
    (hdiagonal : forall seed, 0 <= diagonal seed)
    (hgood : forall seed, seed ∉ bad ->
      p * energy seed <= diagonal seed)
    (hbad : forall seed, seed ∈ bad ->
      energy seed <= envelope seed)
    (hbudget : finiteAverage diagonal +
      p * badEnvelopeAverage bad envelope <= p * target) :
    finiteAverage energy <= target := by
  have hpointwise : forall seed,
      p * energy seed <= diagonal seed +
        p * (if seed ∈ bad then envelope seed else 0) := by
    intro seed
    by_cases hmem : seed ∈ bad
    · rw [if_pos hmem]
      have hp0 : 0 <= p := le_of_lt hp
      have hscaled := mul_le_mul_of_nonneg_left (hbad seed hmem) hp0
      linarith [hdiagonal seed]
    · rw [if_neg hmem, mul_zero, add_zero]
      exact hgood seed hmem
  have hscaled :
      p * finiteAverage energy <=
        finiteAverage diagonal + p * badEnvelopeAverage bad envelope := by
    calc
      p * finiteAverage energy =
          finiteAverage (fun seed => p * energy seed) := by
        rw [finiteAverage_const_mul]
      _ <= finiteAverage (fun seed => diagonal seed +
          p * (if seed ∈ bad then envelope seed else 0)) := by
        exact finiteAverage_mono hpointwise
      _ = finiteAverage diagonal + p * badEnvelopeAverage bad envelope := by
        rw [finiteAverage_add_local, finiteAverage_const_mul]
        rfl
  nlinarith

/-- Density-only corollary.  It is useful when the exceptional masks are
genuinely rare, but is intentionally not claimed to handle coherent behavior
spread across many masks. -/
theorem finiteAverage_energy_le_of_good_bad_density
    {Seed : Type*} [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]
    (bad : Finset Seed) (energy diagonal : Seed -> Rat)
    (p target cap delta : Rat)
    (hp : 0 < p) (hcap0 : 0 <= cap)
    (hdiagonal : forall seed, 0 <= diagonal seed)
    (hgood : forall seed, seed ∉ bad ->
      p * energy seed <= diagonal seed)
    (hbad : forall seed, seed ∈ bad -> energy seed <= cap)
    (hdensity : badSeedDensity bad <= delta)
    (hbudget : finiteAverage diagonal + p * cap * delta <= p * target) :
    finiteAverage energy <= target := by
  have henvelope : badEnvelopeAverage bad (fun _ : Seed => cap) =
      cap * badSeedDensity bad := by
    unfold badEnvelopeAverage badSeedDensity
    rw [← finiteAverage_const_mul]
    apply finiteAverage_congr
    intro seed
    by_cases hmem : seed ∈ bad <;> simp [hmem]
  have hcharge :
      p * badEnvelopeAverage bad (fun _ : Seed => cap) <=
        p * cap * delta := by
    rw [henvelope]
    have hpcap : 0 <= p * cap := mul_nonneg (le_of_lt hp) hcap0
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hdensity hpcap
  apply finiteAverage_energy_le_of_good_bad_envelope
    bad energy diagonal (fun _ => cap) p target hp hdiagonal hgood hbad
  linarith

/-- Exceptional averaging distributes over the mass envelope used below. -/
theorem badEnvelopeAverage_two_mul_add_const
    {Seed : Type*} [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]
    (bad : Finset Seed) (mass : Seed -> Rat) (constant : Rat) :
    badEnvelopeAverage bad (fun seed => 2 * mass seed + 2 * constant) =
      2 * badEnvelopeAverage bad mass +
        2 * constant * badSeedDensity bad := by
  unfold badEnvelopeAverage badSeedDensity
  calc
    finiteAverage (fun seed : Seed =>
        if seed ∈ bad then 2 * mass seed + 2 * constant else 0) =
      finiteAverage (fun seed : Seed =>
        2 * (if seed ∈ bad then mass seed else 0) +
          (2 * constant) * (if seed ∈ bad then 1 else 0)) := by
            apply finiteAverage_congr
            intro seed
            by_cases hmem : seed ∈ bad <;> simp [hmem]
    _ = 2 * finiteAverage (fun seed : Seed =>
          if seed ∈ bad then mass seed else 0) +
        (2 * constant) * finiteAverage (fun seed : Seed =>
          if seed ∈ bad then 1 else 0) := by
            rw [finiteAverage_add_local, finiteAverage_const_mul,
              finiteAverage_const_mul]
    _ = _ := by ring

/-! ## Structured rare-bad-mask certificate -/

/-- High-syndrome energy at one fixed generated mask. -/
def fixedMaskSyndromeEnergy
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  Finset.univ.sum (fun syndrome : StructuredDualPowerSyndrome n m =>
    (structuredSyndromeFiberCoefficientSum n m (2 * m) hn
      f mask syndrome) ^ 2)

/-- Fourier diagonal at one fixed generated mask. -/
def fixedMaskHighDiagonal
    (n m : Nat)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  structuredMaskedHighDiagonalCrossTerm n (2 * m) f f mask

/-- A sufficient rare-bad-mask certificate.  The final inequality explicitly
spends the unused part of the actual diagonal budget on at most `4` units of
energy per exceptional mask. -/
def StructuredRareBadMaskSyndromeFrameCertificate
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (delta : Rat) : Prop :=
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  (forall seed, seed ∉ bad ->
      p * fixedMaskSyndromeEnergy n m hn f (mask seed) <=
        fixedMaskHighDiagonal n m f (mask seed)) ∧
    badSeedDensity bad <= delta ∧
    structuredMaskedHighDiagonalAverage
        n m tailBits (2 * m) hn htail f +
      p * 4 * delta <= p ^ (2 * m + 1)

/-- The rare-bad-mask certificate implies the absolute syndrome-energy
target. -/
theorem structuredSyndromeEnergyAverage_le_pow_of_rareBadMaskCertificate
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : forall input, |f input| <= 1)
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (delta : Rat)
    (hcertificate : StructuredRareBadMaskSyndromeFrameCertificate
      n m tailBits hn htail f bad delta) :
    structuredSyndromeEnergyAverage
        n m tailBits (2 * m) hn htail f <=
      (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  let energy := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    fixedMaskSyndromeEnergy n m hn f (mask seed)
  let diagonal := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    fixedMaskHighDiagonal n m f (mask seed)
  have hp : 0 < p := by dsimp [p]; positivity
  have hdiagonal : forall seed, 0 <= diagonal seed := by
    intro seed
    unfold diagonal fixedMaskHighDiagonal
      structuredMaskedHighDiagonalCrossTerm
    exact Finset.sum_nonneg fun support _ => mul_self_nonneg _
  have hparts := hcertificate
  dsimp only [StructuredRareBadMaskSyndromeFrameCertificate] at hparts
  change (forall seed, seed ∉ bad ->
      p * energy seed <= diagonal seed) ∧
    badSeedDensity bad <= delta ∧
    structuredMaskedHighDiagonalAverage
        n m tailBits (2 * m) hn htail f +
      p * 4 * delta <= p ^ (2 * m + 1) at hparts
  have haverage : finiteAverage energy <= p ^ (2 * m) := by
    apply finiteAverage_energy_le_of_good_bad_density
      bad energy diagonal p (p ^ (2 * m)) 4 delta hp (by norm_num)
      hdiagonal hparts.1
    · intro seed _hseed
      exact fixedMask_syndromeFiberEnergy_le_four
        n m hn f hbounded (mask seed)
    · exact hparts.2.1
    · have hdiagEq : finiteAverage diagonal =
          structuredMaskedHighDiagonalAverage
            n m tailBits (2 * m) hn htail f := by rfl
      rw [hdiagEq]
      rw [show p ^ (2 * m + 1) = p * p ^ (2 * m) by
        rw [pow_succ]; ring] at hparts
      exact hparts.2.2
  simpa [structuredSyndromeEnergyAverage, energy, mask, p] using haverage

/-! ## Mass-weighted bad-mask certificate -/

/-- Conditional selector mass at one mask, averaged only over the structured
base source. -/
def fixedMaskStructuredBaseMass
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (mask : Fin (2 ^ n) -> Bool) : Rat :=
  finiteAverage
    (fun seed : Fin (structuredIndependence m * n) -> Bool =>
      fixedMaskAveragedFunction f mask
        ((structuredUnbiasedPrimitive n m hn).generate seed))

/-- Stronger defective-frame certificate.  Bad masks are charged by their
actual structured conditional acceptance mass (`rho`) plus their density
times the uniform acceptance mass, rather than by the universal constant
cap. -/
def StructuredMassWeightedBadMaskSyndromeFrameCertificate
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (rho delta : Rat) : Prop :=
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  (forall seed, seed ∉ bad ->
      p * fixedMaskSyndromeEnergy n m hn f (mask seed) <=
        fixedMaskHighDiagonal n m f (mask seed)) ∧
    badEnvelopeAverage bad
      (fun seed => fixedMaskStructuredBaseMass n m hn f (mask seed)) <= rho ∧
    badSeedDensity bad <= delta ∧
    structuredMaskedHighDiagonalAverage
        n m tailBits (2 * m) hn htail f +
      p * (2 * rho + 2 * finiteAverage f * delta) <=
        p ^ (2 * m + 1)

/-- The mass-weighted certificate implies the absolute structured syndrome
energy target. -/
theorem structuredSyndromeEnergyAverage_le_pow_of_massWeightedBadMaskCertificate
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hunit : forall input, 0 <= f input ∧ f input <= 1)
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (rho delta : Rat)
    (hcertificate : StructuredMassWeightedBadMaskSyndromeFrameCertificate
      n m tailBits hn htail f bad rho delta) :
    structuredSyndromeEnergyAverage
        n m tailBits (2 * m) hn htail f <=
      (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  let energy := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    fixedMaskSyndromeEnergy n m hn f (mask seed)
  let diagonal := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    fixedMaskHighDiagonal n m f (mask seed)
  let mass := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    fixedMaskStructuredBaseMass n m hn f (mask seed)
  let envelope := fun seed : FiniteBitTape (structuredIndependence m * n) =>
    2 * mass seed + 2 * finiteAverage f
  have hp : 0 < p := by dsimp [p]; positivity
  have hdiagonal : forall seed, 0 <= diagonal seed := by
    intro seed
    unfold diagonal fixedMaskHighDiagonal
      structuredMaskedHighDiagonalCrossTerm
    exact Finset.sum_nonneg fun support _ => mul_self_nonneg _
  have hparts := hcertificate
  dsimp only [StructuredMassWeightedBadMaskSyndromeFrameCertificate]
    at hparts
  change (forall seed, seed ∉ bad ->
      p * energy seed <= diagonal seed) ∧
    badEnvelopeAverage bad mass <= rho ∧
    badSeedDensity bad <= delta ∧
    structuredMaskedHighDiagonalAverage
        n m tailBits (2 * m) hn htail f +
      p * (2 * rho + 2 * finiteAverage f * delta) <=
        p ^ (2 * m + 1) at hparts
  have hmu : 0 <= finiteAverage f :=
    finiteAverage_nonneg fun input => (hunit input).1
  have henvelopeEq : badEnvelopeAverage bad envelope =
      2 * badEnvelopeAverage bad mass +
        2 * finiteAverage f * badSeedDensity bad := by
    exact badEnvelopeAverage_two_mul_add_const
      bad mass (finiteAverage f)
  have hmassScaled :
      2 * badEnvelopeAverage bad mass <= 2 * rho :=
    mul_le_mul_of_nonneg_left hparts.2.1 (by norm_num)
  have hdensityScaled :
      2 * finiteAverage f * badSeedDensity bad <=
        2 * finiteAverage f * delta := by
    exact mul_le_mul_of_nonneg_left hparts.2.2.1
      (mul_nonneg (by norm_num) hmu)
  have henvelope : badEnvelopeAverage bad envelope <=
      2 * rho + 2 * finiteAverage f * delta := by
    rw [henvelopeEq]
    exact add_le_add hmassScaled hdensityScaled
  have hbad : forall seed, seed ∈ bad -> energy seed <= envelope seed := by
    intro seed _hseed
    exact fixedMask_syndromeFiberEnergy_le_two_mul_structuredMass_add_uniformMass
      n m hn f hunit (mask seed)
  have hbudget : finiteAverage diagonal +
      p * badEnvelopeAverage bad envelope <= p * p ^ (2 * m) := by
    have hcharge := mul_le_mul_of_nonneg_left henvelope (le_of_lt hp)
    have hdiagEq : finiteAverage diagonal =
        structuredMaskedHighDiagonalAverage
          n m tailBits (2 * m) hn htail f := by rfl
    rw [hdiagEq]
    rw [show p ^ (2 * m + 1) = p * p ^ (2 * m) by
      rw [pow_succ]; ring] at hparts
    linarith
  have haverage : finiteAverage energy <= p ^ (2 * m) := by
    exact finiteAverage_energy_le_of_good_bad_envelope
      bad energy diagonal envelope p (p ^ (2 * m)) hp
        hdiagonal hparts.1 hbad hbudget
  simpa [structuredSyndromeEnergyAverage, energy, mask, p] using haverage

/-! ## Actual affine-prefixed mandatory selector -/

/-- Rare-bad-mask certificate specialized to the selector which appears
after a fixed affine prefix. -/
def PrefixedMandatoryCanonicalSelectorRareBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (delta : Rat) : Prop :=
  StructuredRareBadMaskSyndromeFrameCertificate
    n m tailBits hn htail
      (FiniteUnambiguousFBDD.ratAcceptanceIndicator
        (prefixedMandatoryCanonicalSelector machine n T b rounds))
    bad delta

/-- The rare-bad-mask selector certificate implies the exact semantic
residual-mass target. -/
theorem residualMassL2Bound_of_prefixedRareBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (delta : Rat)
    (hcertificate : PrefixedMandatoryCanonicalSelectorRareBadMaskCertificate
      machine n T b m tailBits hn htail rounds bad delta) :
    ResidualMassL2Bound machine n T b m tailBits hn htail rounds := by
  let f := (prefixedMandatoryCanonicalSelector machine n T b rounds)
    |>.ratAcceptanceIndicator
  have hbounded : forall input, |f input| <= 1 := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have henergy :=
    structuredSyndromeEnergyAverage_le_pow_of_rareBadMaskCertificate
      n m tailBits hn htail f hbounded bad delta
        (by
          simpa [PrefixedMandatoryCanonicalSelectorRareBadMaskCertificate, f]
            using hcertificate)
  apply (prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound_iff_residualMassL2Bound
    machine n T b m tailBits hn htail rounds).mp
  unfold PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
  simpa [f] using henergy

/-- Consequently the rare-bad-mask certificate gives the card-free one-round
error. -/
theorem oneRoundError_le_pow_of_prefixedRareBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (delta : Rat)
    (hcertificate : PrefixedMandatoryCanonicalSelectorRareBadMaskCertificate
      machine n T b m tailBits hn htail rounds bad delta) :
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
      (residualMassL2Bound_of_prefixedRareBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad delta hcertificate)

/-- Mass-weighted defective-frame certificate for the actual prefixed
selector. -/
def PrefixedMandatoryCanonicalSelectorMassWeightedBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (rho delta : Rat) : Prop :=
  StructuredMassWeightedBadMaskSyndromeFrameCertificate
    n m tailBits hn htail
      (FiniteUnambiguousFBDD.ratAcceptanceIndicator
        (prefixedMandatoryCanonicalSelector machine n T b rounds))
    bad rho delta

/-- The mass-weighted selector certificate implies residual-mass `L2`. -/
theorem residualMassL2Bound_of_prefixedMassWeightedBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (rho delta : Rat)
    (hcertificate :
      PrefixedMandatoryCanonicalSelectorMassWeightedBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad rho delta) :
    ResidualMassL2Bound machine n T b m tailBits hn htail rounds := by
  let f := (prefixedMandatoryCanonicalSelector machine n T b rounds)
    |>.ratAcceptanceIndicator
  have hunit : forall input, 0 <= f input ∧ f input <= 1 := by
    intro input
    unfold f FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have henergy :=
    structuredSyndromeEnergyAverage_le_pow_of_massWeightedBadMaskCertificate
      n m tailBits hn htail f hunit bad rho delta
        (by
          simpa [
            PrefixedMandatoryCanonicalSelectorMassWeightedBadMaskCertificate,
            f] using hcertificate)
  apply (prefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound_iff_residualMassL2Bound
    machine n T b m tailBits hn htail rounds).mp
  unfold PrefixedMandatoryCanonicalSelectorAbsoluteSyndromeEnergyBound
  simpa [f] using henergy

/-- The mass-weighted certificate therefore gives the one-round `p^m`
error bound. -/
theorem oneRoundError_le_pow_of_prefixedMassWeightedBadMaskCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (bad : Finset (FiniteBitTape (structuredIndependence m * n)))
    (rho delta : Rat)
    (hcertificate :
      PrefixedMandatoryCanonicalSelectorMassWeightedBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad rho delta) :
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
      (residualMassL2Bound_of_prefixedMassWeightedBadMaskCertificate
        machine n T b m tailBits hn htail rounds bad rho delta hcertificate)

end MandatoryCanonicalSelectorDefectiveSyndromeFrame
end
end OneTapeMagnification
end Frontier
end Pnp4
