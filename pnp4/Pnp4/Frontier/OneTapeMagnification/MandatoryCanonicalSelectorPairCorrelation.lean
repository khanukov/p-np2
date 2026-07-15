import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorCompleteness
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDConcreteMultiRoundHybrid

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact small-seed pair-correlation target for the mandatory selector

The structured finite-field base source kills every non-dual Walsh pair.  At
cutoff `2 * m`, the exact second moment is therefore a diagonal term plus
`structuredDualFarPairCorrelation`.  The diagonal is already bounded without
any selector-size factor.  This file records the precise remaining signed
inequality and proves that it is sufficient for the actual affine DPTW hybrid.

The correlation premise is deliberately required after **every** fixed affine
prefix.  A bound only for the original selector would not apply at adjacent
steps of the hybrid.  No claim is made here that read-once behavior,
unambiguity, complete query traces, or arbitrary one-tape semantics imply the
premise.  In particular, the theorems below do not assert a universal PRG for
all finite machines; they expose the mathematical obligation rather than
hiding it in a structure or typeclass.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanOneRoundFoolingBound
open FiniteBooleanPerVertexRestrictionBound
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open FiniteAffineRestrictionHybrid

namespace MandatoryCanonicalSelectorPairCorrelation

/-- The mandatory canonical selector after an arbitrary fixed affine prefix.
This is exactly the program which occurs after conditioning on the old seeds
in one adjacent step of the concrete DPTW hybrid. -/
noncomputable abbrev prefixedMandatoryCanonicalSelector
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound (2 ^ n))) :
    FiniteUnambiguousFBDD (2 ^ n) :=
  (mandatoryCanonicalUFBDD machine (2 ^ n) T b)
    |>.affinePaddedRestrictByRounds rounds

/-- The precise signed small-seed selector-pair obligation.

Only an upper bound is required: the dual far sum is signed, and replacing it
by a termwise absolute-value sum would discard exactly the cancellation sought
here.  Since the diagonal is at most `p^(2*m+1)`, the exact remaining budget
for a total second moment at most `p^(2*m)` is
`(1 - p) * p^(2*m)`. -/
def DualFarBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Prop :=
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  structuredDualFarPairCorrelation n m tailBits (2 * m) hn htail
      (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator <=
    (1 - p) * p ^ (2 * m)

/-- The exact dual-far premise removes the selector-size factor from the
structured high-tail second moment, uniformly after a fixed affine prefix. -/
theorem structuredSecondMoment_le_pow_of_dualFarBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hfar : DualFarBound machine n T b m tailBits hn htail rounds) :
    let B := prefixedMandatoryCanonicalSelector machine n T b rounds
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        FiniteUnambiguousFBDD.ratHighDegreeFourierTail
          B.ratAcceptanceIndicator (2 * m)
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
            uniform))) ^ 2) <=
      p ^ (2 * m) := by
  dsimp only
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  have hp0 : 0 <= p := by
    dsimp [p]
    positivity
  have hcutoff : 2 * m + 1 <= structuredIndependence m := by
    unfold structuredIndependence
    omega
  have hbounded : forall input, |f input| <= 1 := by
    intro input
    unfold f B FiniteUnambiguousFBDD.ratAcceptanceIndicator
    split_ifs <;> norm_num
  have hdiag :
      (∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
        (coefficient f support) ^ 2 *
          finiteAverage (fun t : FiniteBitTape (structuredIndependence m * n) =>
            maskAllZeroIndicator support (mask t))) <=
        p ^ (2 * m + 1) := by
    exact highTail_diagonalEnergy_le_pow_succ
      f mask p hp0 hcutoff
        (structuredDyadicPrimitive_patternFalseBiased
          n m tailBits hn htail)
        hbounded
  have hfar' :
      structuredDualFarPairCorrelation n m tailBits (2 * m) hn htail f <=
        (1 - p) * p ^ (2 * m) := by
    simpa [DualFarBound, B, f, p] using hfar
  have hexact :=
    structured_highTail_restriction_secondMoment_eq_diagonal_add_dual
      n m tailBits hn htail f
  change
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
          (maskedInput (D seed.1) (mask seed.2) uniform))) ^ 2) <=
      p ^ (2 * m)
  rw [hexact]
  calc
    (∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
          (coefficient f support) ^ 2 *
            finiteAverage
              (fun t : FiniteBitTape (structuredIndependence m * n) =>
                maskAllZeroIndicator support (mask t))) +
        structuredDualFarPairCorrelation n m tailBits (2 * m)
          hn htail f <=
      p ^ (2 * m + 1) + (1 - p) * p ^ (2 * m) :=
        add_le_add hdiag hfar'
    _ = p ^ (2 * m) := by
      rw [show 2 * m + 1 = 2 * m + 1 by rfl, pow_succ]
      ring

/-- Cauchy--Schwarz and exact low-degree cancellation turn the preceding
second-moment bound into the one-round error `p^m`, with no vertex or
component count. -/
theorem oneRoundError_le_pow_of_dualFarBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hfar : DualFarBound machine n T b m tailBits hn htail rounds) :
    let B := prefixedMandatoryCanonicalSelector machine n T b rounds
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          B.ratAcceptanceIndicator
            (maskedInput
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
              uniform))) -
      finiteAverage B.ratAcceptanceIndicator| <=
        p ^ m := by
  dsimp only
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let f := B.ratAcceptanceIndicator
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  have hDlow : IsKWisePatternUnbiased (2 * m) D := by
    apply isKWisePatternUnbiased_of_le (large := structuredIndependence m)
    · unfold structuredIndependence
      omega
    · exact structuredUnbiasedPrimitive_patternUnbiased n m hn
  have hexact := oneRoundAverage_eq_uniformAverage_add_highDegreeAverage
    f D mask hDlow
  have hgap :
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          f (maskedInput (D seed.1) (mask seed.2) uniform))) -
          finiteAverage f =
        finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
          finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
            FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
              (maskedInput (D seed.1) (mask seed.2) uniform))) := by
    rw [hexact]
    ring
  have hsecond := structuredSecondMoment_le_pow_of_dualFarBound
    machine n T b m tailBits hn htail rounds hfar
  dsimp only at hsecond
  change
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
          (maskedInput (D seed.1) (mask seed.2) uniform))) ^ 2) <=
      p ^ (2 * m) at hsecond
  let tailAverage := fun seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n) =>
    finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
      FiniteUnambiguousFBDD.ratHighDegreeFourierTail f (2 * m)
        (maskedInput (D seed.1) (mask seed.2) uniform))
  have habsSquare :
      (finiteAverage (fun seed => |tailAverage seed|)) ^ 2 <=
        p ^ (2 * m) :=
    (finiteAverage_abs_sq_le_average_sq tailAverage).trans hsecond
  have hp0 : 0 <= p ^ m := by positivity
  have havg0 : 0 <= finiteAverage (fun seed => |tailAverage seed|) := by
    exact finiteAverage_nonneg fun seed => abs_nonneg _
  have habs : finiteAverage (fun seed => |tailAverage seed|) <= p ^ m := by
    apply FiniteBooleanVertexSumRestrictionBound.le_of_sq_le_sq_of_nonneg
      havg0 hp0
    simpa [show 2 * m = m + m by omega, pow_add, pow_two] using habsSquare
  change
    |finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          f (maskedInput (D seed.1) (mask seed.2) uniform))) -
      finiteAverage f| <= p ^ m
  rw [hgap]
  calc
    |finiteAverage tailAverage| <=
        finiteAverage (fun seed => |tailAverage seed|) :=
      abs_finiteAverage_le_finiteAverage_abs tailAverage
    _ <= p ^ m := habs

/-- The exact hybrid-facing selector-pair obligation.

Unlike `DualFarBound` for every arbitrary affine list, this proposition only
quantifies over prefixes which the concrete structured generator can actually
produce.  This is the weakest prefix-stability interface needed by the
multi-round hybrid below. -/
def GeneratedPrefixDualFarBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n) : Prop :=
  forall (r : Nat)
    (oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r),
    DualFarBound machine n T b m tailBits hn htail
      (roundsOfSeeds
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate
        r oldSeeds)

/-- The exact finite-hybrid obligation: only generated prefixes strictly
before round `L` are required. -/
def GeneratedPrefixDualFarBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) : Prop :=
  forall (r : Nat), r < L ->
    forall oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      DualFarBound machine n T b m tailBits hn htail
        (roundsOfSeeds
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate
          r oldSeeds)

/-- A global generated-prefix bound implies every finite-prefix version. -/
theorem generatedPrefixDualFarBoundUpTo_of_generatedPrefixDualFarBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hfar : GeneratedPrefixDualFarBound
      machine n T b m tailBits hn htail) :
    GeneratedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail := by
  intro r _hr oldSeeds
  exact hfar r oldSeeds

/-- A bound for all affine prefixes is a convenient sufficient condition for
the strictly weaker generated-prefix obligation. -/
theorem generatedPrefixDualFarBound_of_allDualFarBounds
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (hfar : forall rounds : List (AffineRestrictionRound (2 ^ n)),
      DualFarBound machine n T b m tailBits hn htail rounds) :
    GeneratedPrefixDualFarBound machine n T b m tailBits hn htail := by
  intro r oldSeeds
  exact hfar _

/-- A pointwise bound for the generated prefixes at one fixed depth controls
that adjacent structured hybrid step. -/
theorem abs_value_succ_sub_value_le_pow_of_generatedPrefixDualFarBoundAt
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits r : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hfar : forall oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      DualFarBound machine n T b m tailBits hn htail
        (roundsOfSeeds
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate
          r oldSeeds)) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask (r + 1) - value B D mask r| <= p ^ m := by
  dsimp only
  rw [value_succ_eq_prefixAverage_oneRound]
  unfold value
  rw [<- finiteAverage_sub]
  apply abs_finiteAverage_le_of_pointwise_abs_le
  intro oldSeeds
  exact oneRoundError_le_pow_of_dualFarBound
    machine n T b m tailBits hn htail
      (roundsOfSeeds
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate
        r oldSeeds)
      (hfar oldSeeds)

/-- Generated-prefix dual correlation controls every adjacent structured
hybrid step by `p^m`, independently of the selector's vertex count. -/
theorem abs_value_succ_sub_value_le_pow_of_generatedPrefixDualFarBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits r : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hfar : GeneratedPrefixDualFarBound
      machine n T b m tailBits hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask (r + 1) - value B D mask r| <= p ^ m := by
  exact abs_value_succ_sub_value_le_pow_of_generatedPrefixDualFarBoundAt
    machine n T b m tailBits r hn htail (hfar r)

/-- For an `L`-round hybrid it is enough to assume the selector correlation
bound only at the generated prefix depths `r < L`. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBoundUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hfar : GeneratedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| <= (L : Rat) * p ^ m := by
  dsimp only
  apply FiniteRoundTelescoping.abs_value_sub_initial_le_rounds_mul
  intro round hround
  exact abs_value_succ_sub_value_le_pow_of_generatedPrefixDualFarBoundAt
    machine n T b m tailBits round hn htail (hfar round hround)

/-- Telescoping the preceding adjacent-step estimate gives the card-free
multi-round Fourier error.  The independent zero-tail survivor term can be
added by the existing DPTW packing/survivor bridge. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBound
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hfar : GeneratedPrefixDualFarBound
      machine n T b m tailBits hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| <= (L : Rat) * p ^ m := by
  exact
    abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail
        (generatedPrefixDualFarBoundUpTo_of_generatedPrefixDualFarBound
          machine n T b m tailBits L hn htail hfar)

/-- Requiring the signed dual-far bound after every affine prefix is a useful
strong sufficient version of the adjacent generated-prefix theorem. -/
theorem abs_value_succ_sub_value_le_pow_of_allDualFarBounds
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits r : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hfar : forall rounds : List (AffineRestrictionRound (2 ^ n)),
      DualFarBound machine n T b m tailBits hn htail rounds) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask (r + 1) - value B D mask r| <= p ^ m := by
  exact abs_value_succ_sub_value_le_pow_of_generatedPrefixDualFarBound
    machine n T b m tailBits r hn htail
      (generatedPrefixDualFarBound_of_allDualFarBounds
        machine n T b m tailBits hn htail hfar)

/-- The all-affine-prefix hypothesis also implies the concrete card-free
multi-round estimate, via the weaker generated-prefix interface. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_allDualFarBounds
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (hfar : forall rounds : List (AffineRestrictionRound (2 ^ n)),
      DualFarBound machine n T b m tailBits hn htail rounds) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| <= (L : Rat) * p ^ m := by
  exact
    abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBound
      machine n T b m tailBits L hn htail
        (generatedPrefixDualFarBound_of_allDualFarBounds
          machine n T b m tailBits hn htail hfar)

end MandatoryCanonicalSelectorPairCorrelation
end

end OneTapeMagnification
end Frontier
end Pnp4
