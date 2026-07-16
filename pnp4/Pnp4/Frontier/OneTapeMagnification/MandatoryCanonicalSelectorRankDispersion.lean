import Pnp4.Frontier.OneTapeMagnification.FiniteStructuredDualRankThresholdBridge
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact rank dispersion of a mandatory canonical selector

The cumulative-four statement is false for arbitrary Boolean functions and
arbitrary read-once branching programs.  For a fixed finite one-tape machine,
however, the remaining signed obstruction is a finite, machine-specific
number.  This file defines that number without an existential hypothesis:
it is the maximum of zero and all strict-intermediate structured rank
partial sums of the actual prefixed mandatory selector.

The resulting `selectorStructuredDualRankStrictDispersion` is the least
nonnegative cap for those partial sums.  Thus bounding it by `4` is exactly
equivalent to the still-open strict-intermediate cumulative-four statement for
that fixed prefix, and implies its existing `DualFarBound`.  The corresponding
families of dispersion bounds over generated prefixes imply the generated-
prefix and finite-round hybrid interfaces.  No cardinality, positivity, or
absolute-value relaxation is hidden in the definition.

The machine-state and running-time geometry has not yet been used to prove
the numerical inequality `dispersion <= 4`.  Establishing that implication
for fixed-state near-linear one-tape machines is the remaining lower-layer
problem isolated here.
-/

noncomputable section

open FiniteAffineRestrictionHybrid
open DPTWStructuredFieldCoordinatePrimitive
open MandatoryCanonicalSelectorPairCorrelation
open FiniteStructuredDualRankThresholdBridge

namespace MandatoryCanonicalSelectorRankDispersion

/-- The actual `T`-step cached one-tape acceptance bit after applying an
affine prefix to the input.  This exposes the transition semantics behind the
selector rather than treating its uFBDD representation as an arbitrary
Boolean function. -/
noncomputable def affinePrefixedCachedRunAcceptanceIndicator
    (machine : DeterministicMachine) (n T : Nat)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (input : Fin (2 ^ n) -> Bool) : Rat := by
  classical
  exact if IsAccepting (cachedInputMachine machine)
      (run (cachedInputMachine machine)
        (List.ofFn (applyAffineRestrictionRounds rounds input)) T) then
    1
  else
    0

/-- Transporting the input arity along an equality only transports the input
function; it does not change mandatory-selector acceptance. -/
theorem mandatoryCanonicalUFBDD_accepts_cast_input_arity
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (leftN rightN T b : Nat) (h : leftN = rightN)
    (input : Fin leftN -> Bool) :
    (mandatoryCanonicalUFBDD machine leftN T b).Accepts input ↔
      (mandatoryCanonicalUFBDD machine rightN T b).Accepts
        (fun coordinate => input (Fin.cast h.symm coordinate)) := by
  subst rightN
  rfl

/-- For positive block size, the prefixed mandatory selector is extensionally
the real cached-machine run predicate on the recursively masked input. -/
theorem prefixedMandatoryCanonicalSelector_ratAcceptanceIndicator_eq_cachedRun
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (input : Fin (2 ^ n) -> Bool) :
    (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator input =
      affinePrefixedCachedRunAcceptanceIndicator
        machine n T rounds input := by
  classical
  rw [FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq]
  let masked := applyAffineRestrictionRounds rounds input
  have hsemantics :
      (mandatoryCanonicalUFBDD machine (2 ^ n) T b).Accepts masked ↔
        IsAccepting (cachedInputMachine machine)
          (run (cachedInputMachine machine) (List.ofFn masked) T) := by
    have hraw := mandatoryCanonicalUFBDD_accepts_iff_cached_acceptance
      machine (List.ofFn masked) T b hb
    have hlength : (List.ofFn masked).length = 2 ^ n := List.length_ofFn
    have hcast := mandatoryCanonicalUFBDD_accepts_cast_input_arity
      machine (List.ofFn masked).length (2 ^ n) T b hlength
        (fun coordinate => (List.ofFn masked).get coordinate)
    have hinput :
        (fun coordinate : Fin (2 ^ n) =>
          (List.ofFn masked).get (Fin.cast hlength.symm coordinate)) =
        masked := by
      funext coordinate
      simp only [List.get_ofFn]
      congr 1
    have hcast' :
        ((mandatoryCanonicalUFBDD machine (List.ofFn masked).length T b).Accepts
            fun coordinate => (List.ofFn masked).get coordinate) ↔
          (mandatoryCanonicalUFBDD machine (2 ^ n) T b).Accepts masked := by
      simpa only [hinput] using hcast
    exact hcast'.symm.trans hraw
  unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    affinePrefixedCachedRunAcceptanceIndicator
  change (if (mandatoryCanonicalUFBDD machine (2 ^ n) T b).Accepts masked
      then 1 else 0) =
    (if IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) (List.ofFn masked) T)
      then 1 else 0)
  by_cases haccepts :
      (mandatoryCanonicalUFBDD machine (2 ^ n) T b).Accepts masked
  · rw [if_pos haccepts, if_pos (hsemantics.mp haccepts)]
  · rw [if_neg haccepts, if_neg (fun hrun => haccepts (hsemantics.mpr hrun))]

/-- The finite set consisting of zero and every strict-intermediate signed
rank-threshold sum of the actual prefixed mandatory selector.  Including zero
makes the resulting maximum canonical even when the rank interval is empty
and records that the dispersion is a nonnegative parameter. -/
noncomputable def selectorStructuredDualRankStrictValues
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Finset Rat := by
  classical
  let f :=
    (prefixedMandatoryCanonicalSelector machine n T b rounds)
      |>.ratAcceptanceIndicator
  exact insert 0 <|
    (Finset.Ico
      (structuredIndependence m * tailBits)
      (structuredIndependence m * n)).image fun level =>
        structuredDualRankAtMostCrossForm
          n m tailBits (2 * m) hn htail f f level

/-- Positive block size rewrites the entire finite value set to the Fourier
rank-threshold sums of the actual affine-prefixed machine-run predicate. -/
theorem selectorStructuredDualRankStrictValues_eq_cachedRun
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    selectorStructuredDualRankStrictValues
        machine n T b m tailBits hn htail rounds =
      insert 0
        ((Finset.Ico
          (structuredIndependence m * tailBits)
          (structuredIndependence m * n)).image fun level =>
            structuredDualRankAtMostCrossForm
              n m tailBits (2 * m) hn htail
              (affinePrefixedCachedRunAcceptanceIndicator machine n T rounds)
              (affinePrefixedCachedRunAcceptanceIndicator machine n T rounds)
              level) := by
  classical
  have hf :
      (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator =
        affinePrefixedCachedRunAcceptanceIndicator machine n T rounds :=
    funext fun input =>
      prefixedMandatoryCanonicalSelector_ratAcceptanceIndicator_eq_cachedRun
        machine n T b hb rounds input
  unfold selectorStructuredDualRankStrictValues
  dsimp only
  rw [hf]

theorem selectorStructuredDualRankStrictValues_nonempty
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    (selectorStructuredDualRankStrictValues
      machine n T b m tailBits hn htail rounds).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp [selectorStructuredDualRankStrictValues]

/-- Exact machine-and-prefix rank dispersion: the maximum positive signed
strict-intermediate cumulative excursion, clipped below at zero. -/
noncomputable def selectorStructuredDualRankStrictDispersion
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) : Rat :=
  (selectorStructuredDualRankStrictValues
    machine n T b m tailBits hn htail rounds).max'
      (selectorStructuredDualRankStrictValues_nonempty
        machine n T b m tailBits hn htail rounds)

/-- Transition-semantic form of the exact dispersion.  For `b > 0`, the
maximum can be computed directly from the cached machine's `T`-step run
predicate after the affine prefix. -/
theorem selectorStructuredDualRankStrictDispersion_eq_cachedRunMax
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hb : 0 < b)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    selectorStructuredDualRankStrictDispersion
        machine n T b m tailBits hn htail rounds =
      (insert 0
        ((Finset.Ico
          (structuredIndependence m * tailBits)
          (structuredIndependence m * n)).image fun level =>
            structuredDualRankAtMostCrossForm
              n m tailBits (2 * m) hn htail
              (affinePrefixedCachedRunAcceptanceIndicator machine n T rounds)
              (affinePrefixedCachedRunAcceptanceIndicator machine n T rounds)
              level)).max' (by simp) := by
  unfold selectorStructuredDualRankStrictDispersion
  let cachedValues : Finset Rat :=
    insert 0
      ((Finset.Ico
        (structuredIndependence m * tailBits)
        (structuredIndependence m * n)).image fun level =>
          structuredDualRankAtMostCrossForm
            n m tailBits (2 * m) hn htail
            (affinePrefixedCachedRunAcceptanceIndicator machine n T rounds)
            (affinePrefixedCachedRunAcceptanceIndicator machine n T rounds)
            level)
  have hvalues :
      selectorStructuredDualRankStrictValues
          machine n T b m tailBits hn htail rounds = cachedValues := by
    exact selectorStructuredDualRankStrictValues_eq_cachedRun
      machine n T b m tailBits hn hb htail rounds
  change
    (selectorStructuredDualRankStrictValues
      machine n T b m tailBits hn htail rounds).max' _ =
      cachedValues.max' _
  apply le_antisymm
  · apply Finset.max'_le
    intro value hvalue
    apply Finset.le_max'
    rw [← hvalues]
    exact hvalue
  · apply Finset.max'_le
    intro value hvalue
    apply Finset.le_max'
    rw [hvalues]
    exact hvalue

/-- The exact dispersion is nonnegative, including for an empty strict rank
interval. -/
theorem selectorStructuredDualRankStrictDispersion_nonneg
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    0 <= selectorStructuredDualRankStrictDispersion
      machine n T b m tailBits hn htail rounds := by
  classical
  unfold selectorStructuredDualRankStrictDispersion
  apply Finset.le_max'
  simp [selectorStructuredDualRankStrictValues]

/-- Every actual strict-intermediate signed partial sum is bounded by the
machine-specific dispersion, by definition of the finite maximum. -/
theorem structuredDualRankAtMostCrossForm_le_selectorStrictDispersion
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits level : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hbase : structuredIndependence m * tailBits <= level)
    (hstrict : level < structuredIndependence m * n) :
    let f :=
      (prefixedMandatoryCanonicalSelector machine n T b rounds)
        |>.ratAcceptanceIndicator
    structuredDualRankAtMostCrossForm
        n m tailBits (2 * m) hn htail f f level <=
      selectorStructuredDualRankStrictDispersion
        machine n T b m tailBits hn htail rounds := by
  classical
  dsimp only
  unfold selectorStructuredDualRankStrictDispersion
  apply Finset.le_max'
  simp only [selectorStructuredDualRankStrictValues, Finset.mem_insert,
    Finset.mem_image]
  right
  exact ⟨level, Finset.mem_Ico.mpr ⟨hbase, hstrict⟩, rfl⟩

/-- The dispersion itself supplies an unconditional strict-intermediate
cumulative bound. -/
theorem structuredDualRankStrictIntermediateCumulativeBound_at_dispersion
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    let f :=
      (prefixedMandatoryCanonicalSelector machine n T b rounds)
        |>.ratAcceptanceIndicator
    StructuredDualRankStrictIntermediateCumulativeBound
      n m tailBits (2 * m) hn htail f f
        (selectorStructuredDualRankStrictDispersion
          machine n T b m tailBits hn htail rounds) := by
  dsimp only
  intro level hbase hstrict
  exact structuredDualRankAtMostCrossForm_le_selectorStrictDispersion
    machine n T b m tailBits level hn htail rounds hbase hstrict

/-- Exact minimal-cap characterization.  A rational `cap` bounds the
dispersion iff it is nonnegative and bounds every strict-intermediate signed
rank partial sum. -/
theorem selectorStructuredDualRankStrictDispersion_le_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) (cap : Rat) :
    selectorStructuredDualRankStrictDispersion
        machine n T b m tailBits hn htail rounds <= cap ↔
      0 <= cap ∧
        StructuredDualRankStrictIntermediateCumulativeBound
          n m tailBits (2 * m) hn htail
          (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
          (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
          cap := by
  classical
  constructor
  · intro hdispersion
    constructor
    · exact (selectorStructuredDualRankStrictDispersion_nonneg
        machine n T b m tailBits hn htail rounds).trans hdispersion
    · intro level hbase hstrict
      exact (structuredDualRankAtMostCrossForm_le_selectorStrictDispersion
        machine n T b m tailBits level hn htail rounds hbase hstrict).trans
          hdispersion
  · rintro ⟨hcap, hcumulative⟩
    unfold selectorStructuredDualRankStrictDispersion
    apply Finset.max'_le
    intro value hvalue
    simp only [selectorStructuredDualRankStrictValues, Finset.mem_insert,
      Finset.mem_image] at hvalue
    rcases hvalue with hzero | ⟨level, hlevel, hvalue⟩
    · simpa [hzero] using hcap
    · subst value
      exact hcumulative level
        (Finset.mem_Ico.mp hlevel).1 (Finset.mem_Ico.mp hlevel).2

/-- Consequently, the concrete numerical target `dispersion <= 4` is not a
new hidden premise: it is exactly the strict-intermediate cumulative-four
statement for this machine and affine prefix. -/
theorem selectorStructuredDualRankStrictDispersion_le_four_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    selectorStructuredDualRankStrictDispersion
        machine n T b m tailBits hn htail rounds <= 4 ↔
      StructuredDualRankStrictIntermediateCumulativeBound
        n m tailBits (2 * m) hn htail
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
        4 := by
  rw [selectorStructuredDualRankStrictDispersion_le_iff]
  norm_num

/-- The acceptance indicator of every prefixed mandatory selector is
pointwise one-bounded. -/
theorem prefixedMandatoryCanonicalSelector_ratAcceptanceIndicator_abs_le_one
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound (2 ^ n)))
    (input : Fin (2 ^ n) -> Bool) :
    |(prefixedMandatoryCanonicalSelector machine n T b rounds)
        |>.ratAcceptanceIndicator input| <= 1 := by
  unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
  split_ifs <;> norm_num

/-- Fixed-prefix capstone: a numerical bound on the exact selector
dispersion supplies the full cumulative-four criterion (using the
unconditional terminal estimate) and hence the existing `DualFarBound`. -/
theorem dualFarBound_of_selectorStructuredDualRankStrictDispersion_le_four
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hdispersion :
      selectorStructuredDualRankStrictDispersion
        machine n T b m tailBits hn htail rounds <= 4) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  apply dualFarBound_of_structuredDualRankCumulativeFour
    machine n T b m tailBits hn hm htailPos htail rounds
  apply
    (structuredDualRankCumulativeBound_four_iff_strictIntermediate_of_bounded
      n m tailBits hn htail
      (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
      (prefixedMandatoryCanonicalSelector_ratAcceptanceIndicator_abs_le_one
        machine n T b rounds)).2
  exact
    (selectorStructuredDualRankStrictDispersion_le_four_iff
      machine n T b m tailBits hn htail rounds).mp hdispersion

/-- Generated-prefix version of the explicit numerical target.  It only
quantifies over affine prefixes produced by the concrete structured hybrid. -/
def GeneratedPrefixSelectorStructuredDualRankStrictDispersionFour
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n) : Prop :=
  forall (r : Nat)
    (oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r),
    selectorStructuredDualRankStrictDispersion
      machine n T b m tailBits hn htail
      (roundsOfSeeds
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate
        r oldSeeds) <= 4

/-- The generated-prefix dispersion-four target implies the exact
generated-prefix pair-correlation obligation used by every hybrid step. -/
theorem generatedPrefixDualFarBound_of_selectorRankStrictDispersionFour
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (hdispersion :
      GeneratedPrefixSelectorStructuredDualRankStrictDispersionFour
        machine n T b m tailBits hn htail) :
    GeneratedPrefixDualFarBound machine n T b m tailBits hn htail := by
  intro r oldSeeds
  exact dualFarBound_of_selectorStructuredDualRankStrictDispersion_le_four
    machine n T b m tailBits hn hm htailPos htail
    (roundsOfSeeds
      (structuredUnbiasedPrimitive n m hn).generate
      (structuredDyadicPrimitive n m tailBits hn htail).generate
      r oldSeeds)
    (hdispersion r oldSeeds)

/-- Finite-depth generated-prefix version, matching the weakest premise of an
`L`-round hybrid. -/
def GeneratedPrefixSelectorStructuredDualRankStrictDispersionFourUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n)
    (htail : tailBits <= n) : Prop :=
  forall (r : Nat), r < L ->
    forall oldSeeds : Seeds
      (FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n)) r,
      selectorStructuredDualRankStrictDispersion
        machine n T b m tailBits hn htail
        (roundsOfSeeds
          (structuredUnbiasedPrimitive n m hn).generate
          (structuredDyadicPrimitive n m tailBits hn htail).generate
          r oldSeeds) <= 4

/-- The finite-depth dispersion target implies exactly the finite-depth
generated-prefix dual-far premise. -/
theorem generatedPrefixDualFarBoundUpTo_of_selectorRankStrictDispersionFourUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (hdispersion :
      GeneratedPrefixSelectorStructuredDualRankStrictDispersionFourUpTo
        machine n T b m tailBits L hn htail) :
    GeneratedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail := by
  intro r hr oldSeeds
  exact dualFarBound_of_selectorStructuredDualRankStrictDispersion_le_four
    machine n T b m tailBits hn hm htailPos htail
    (roundsOfSeeds
      (structuredUnbiasedPrimitive n m hn).generate
      (structuredDyadicPrimitive n m tailBits hn htail).generate
      r oldSeeds)
    (hdispersion r hr oldSeeds)

/-- Direct hybrid-facing capstone: the finite collection of explicit
machine-dispersion inequalities controls the complete `L`-round Fourier
error with no selector-size factor. -/
theorem abs_value_sub_value_zero_le_rounds_mul_pow_of_selectorRankStrictDispersionFourUpTo
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits L : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (hdispersion :
      GeneratedPrefixSelectorStructuredDualRankStrictDispersionFourUpTo
        machine n T b m tailBits L hn htail) :
    let B := mandatoryCanonicalUFBDD machine (2 ^ n) T b
    let D := (structuredUnbiasedPrimitive n m hn).generate
    let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |value B D mask L - value B D mask 0| <= (L : Rat) * p ^ m := by
  exact
    abs_value_sub_value_zero_le_rounds_mul_pow_of_generatedPrefixDualFarBoundUpTo
      machine n T b m tailBits L hn htail
      (generatedPrefixDualFarBoundUpTo_of_selectorRankStrictDispersionFourUpTo
        machine n T b m tailBits L hn hm htailPos htail hdispersion)

end MandatoryCanonicalSelectorRankDispersion
end

end OneTapeMagnification
end Frontier
end Pnp4
