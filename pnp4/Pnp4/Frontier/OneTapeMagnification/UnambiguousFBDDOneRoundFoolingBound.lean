import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDOneRoundHighDegreeBound
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Full one-round fooling bound for finite canonical uFBDDs

This module closes the low-degree half of one masked restriction round.  Exact
Fourier inversion splits a rational Boolean-cube function into its constant
coefficient, the nonempty supports of degree at most the cutoff, and the
strictly higher-degree tail.  A pattern-unbiased base source cancels every
displayed nonempty low-degree character after averaging over the independent
base and mask seeds.  Combining this exact cancellation with the existing
uFBDD high-tail estimate gives a genuine one-round acceptance-probability
bound.

Nothing here iterates the restriction.  In particular, the full-read premise
is retained explicitly for a general uFBDD and discharged only for the
mandatory canonical program.
-/

namespace FiniteBooleanOneRoundFoolingBound

open scoped BigOperators
open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanPerVertexRestrictionBound
open FiniteUnambiguousFBDD

/-! ## Exact Fourier trichotomy -/

/-- The nonconstant Fourier part whose supports have degree at most `k`. -/
noncomputable def ratLowDegreeNonemptyFourierPart {n : Nat}
    (f : (Fin n → Bool) → ℚ) (k : Nat) (input : Fin n → Bool) : ℚ :=
  ∑ alpha : Finset (Fin n),
    if alpha.Nonempty ∧ alpha.card ≤ k then
      coefficient f alpha * character alpha input
    else 0

/-- Exact Fourier inversion split into the constant coefficient, the
nonempty degrees at most `k`, and the strict degree-`> k` tail. -/
theorem fourier_inversion_eq_constant_add_lowDegreeNonempty_add_highDegree
    {n k : Nat} (f : (Fin n → Bool) → ℚ) (input : Fin n → Bool) :
    f input =
      coefficient f ∅ +
        ratLowDegreeNonemptyFourierPart f k input +
          ratHighDegreeFourierTail f k input := by
  classical
  rw [← fourier_inversion f input]
  simp only [ratLowDegreeNonemptyFourierPart, ratHighDegreeFourierTail]
  calc
    (∑ alpha : Finset (Fin n),
        coefficient f alpha * character alpha input) =
        ∑ alpha : Finset (Fin n),
          ((if alpha = ∅ then coefficient f alpha * character alpha input else 0) +
            (if alpha.Nonempty ∧ alpha.card ≤ k then
              coefficient f alpha * character alpha input else 0) +
            (if k < alpha.card then
              coefficient f alpha * character alpha input else 0)) := by
      apply Finset.sum_congr rfl
      intro alpha _
      by_cases hempty : alpha = ∅
      · subst alpha
        simp
      · have hnonempty : alpha.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        by_cases hcard : alpha.card ≤ k
        · simp [hempty, hnonempty, hcard, Nat.not_lt_of_ge hcard]
        · have hhigh : k < alpha.card := Nat.lt_of_not_ge hcard
          simp [hempty, hnonempty, hcard, hhigh]
    _ =
        (∑ alpha : Finset (Fin n),
          if alpha = ∅ then coefficient f alpha * character alpha input else 0) +
          (∑ alpha : Finset (Fin n),
            if alpha.Nonempty ∧ alpha.card ≤ k then
              coefficient f alpha * character alpha input else 0) +
          (∑ alpha : Finset (Fin n),
            if k < alpha.card then
              coefficient f alpha * character alpha input else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = coefficient f ∅ +
          (∑ alpha : Finset (Fin n),
            if alpha.Nonempty ∧ alpha.card ≤ k then
              coefficient f alpha * character alpha input else 0) +
          (∑ alpha : Finset (Fin n),
            if k < alpha.card then
              coefficient f alpha * character alpha input else 0) := by
      simp

/-- The constant Fourier coefficient is exactly the uniform cube average. -/
theorem coefficient_empty_eq_finiteAverage {n : Nat}
    (f : (Fin n → Bool) → ℚ) :
    coefficient f ∅ = finiteAverage f := by
  rw [coefficient_eq_finiteAverage_mul]
  apply finiteAverage_congr
  intro input
  simp

/-! ## Elementary linearity of the exact finite average -/

theorem finiteAverage_add {Seed : Type*} [Fintype Seed]
    (f g : Seed → ℚ) :
    finiteAverage (fun seed => f seed + g seed) =
      finiteAverage f + finiteAverage g := by
  unfold finiteAverage
  rw [Finset.sum_add_distrib]
  ring

theorem finiteAverage_sub {Seed : Type*} [Fintype Seed]
    (f g : Seed → ℚ) :
    finiteAverage (fun seed => f seed - g seed) =
      finiteAverage f - finiteAverage g := by
  unfold finiteAverage
  rw [Finset.sum_sub_distrib]
  ring

/-- Exact finite averages commute with a sum over an entire finite type. -/
theorem finiteAverage_fintype_sum {Seed Index : Type*}
    [Fintype Seed] [Fintype Index] (f : Index → Seed → ℚ) :
    finiteAverage (fun seed => ∑ index : Index, f index seed) =
      ∑ index : Index, finiteAverage (f index) := by
  unfold finiteAverage
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

/-! ## Exact cancellation of all nonempty low degrees -/

/-- After the uniform live fill, a restricted character has mean equal to its
base character times the all-frozen mask indicator. -/
theorem finiteAverage_character_maskedInput_eq_character_mul_indicator
    {n : Nat} (alpha : Finset (Fin n))
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
      character alpha (maskedInput base mask uniform)) =
      character alpha base * maskAllZeroIndicator alpha mask := by
  exact restrictedCharacterAverage_eq alpha base mask

/-- Independence of the base and mask seeds lets the zero base-character
moment cancel a nonempty restricted character.  No distributional premise on
the mask is needed for this low-degree identity. -/
theorem finiteAverage_restrictedCharacter_eq_zero_of_patternUnbiased
    {n q : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased q D)
    (alpha : Finset (Fin n)) (hcard : alpha.card ≤ q)
    (hnonempty : alpha.Nonempty) :
    finiteAverage (fun seed : DSeed × TSeed =>
      finiteAverage (fun uniform : Fin n → Bool =>
        character alpha
          (maskedInput (D seed.1) (T seed.2) uniform))) = 0 := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          character alpha
            (maskedInput (D seed.1) (T seed.2) uniform))) =
        finiteAverage (fun seed : DSeed × TSeed =>
          character alpha (D seed.1) *
            maskAllZeroIndicator alpha (T seed.2)) := by
      apply finiteAverage_congr
      intro seed
      exact finiteAverage_character_maskedInput_eq_character_mul_indicator
        alpha (D seed.1) (T seed.2)
    _ = finiteAverage (fun d : DSeed => character alpha (D d)) *
          finiteAverage (fun t : TSeed =>
            maskAllZeroIndicator alpha (T t)) :=
      FiniteBooleanRestrictionMoment.finiteAverage_prod_mul
        (Left := DSeed) (Right := TSeed)
        (fun d : DSeed => character alpha (D d))
        (fun t : TSeed => maskAllZeroIndicator alpha (T t))
    _ = 0 := by
      rw [character_average_eq_zero_of_patternUnbiased
        D hD alpha hcard hnonempty, zero_mul]

/-- Every nonempty Fourier support of degree at most `k` cancels exactly in
one masked round when the base source is `k`-wise pattern-unbiased. -/
theorem ratLowDegreeNonemptyFourierPart_oneRoundAverage_eq_zero
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased k D) :
    finiteAverage (fun seed : DSeed × TSeed =>
      finiteAverage (fun uniform : Fin n → Bool =>
        ratLowDegreeNonemptyFourierPart f k
          (maskedInput (D seed.1) (T seed.2) uniform))) = 0 := by
  classical
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          ratLowDegreeNonemptyFourierPart f k
            (maskedInput (D seed.1) (T seed.2) uniform))) =
        finiteAverage (fun seed : DSeed × TSeed =>
          ∑ alpha : Finset (Fin n),
            if alpha.Nonempty ∧ alpha.card ≤ k then
              coefficient f alpha *
                finiteAverage (fun uniform : Fin n → Bool =>
                  character alpha
                    (maskedInput (D seed.1) (T seed.2) uniform))
            else 0) := by
      simp only [ratLowDegreeNonemptyFourierPart]
      apply finiteAverage_congr
      intro seed
      rw [finiteAverage_fintype_sum]
      apply Finset.sum_congr rfl
      intro alpha _
      by_cases hlow : alpha.Nonempty ∧ alpha.card ≤ k
      · simp_rw [if_pos hlow]
        rw [finiteAverage_const_mul]
      · simp_rw [if_neg hlow]
        exact
          FiniteBooleanPerVertexRestrictionBound.finiteAverage_const 0
    _ = ∑ alpha : Finset (Fin n),
          finiteAverage (fun seed : DSeed × TSeed =>
            if alpha.Nonempty ∧ alpha.card ≤ k then
              coefficient f alpha *
                finiteAverage (fun uniform : Fin n → Bool =>
                  character alpha
                    (maskedInput (D seed.1) (T seed.2) uniform))
            else 0) := by
      rw [finiteAverage_fintype_sum]
    _ = ∑ alpha : Finset (Fin n),
          if alpha.Nonempty ∧ alpha.card ≤ k then
            coefficient f alpha *
              finiteAverage (fun seed : DSeed × TSeed =>
                finiteAverage (fun uniform : Fin n → Bool =>
                  character alpha
                    (maskedInput (D seed.1) (T seed.2) uniform)))
          else 0 := by
      apply Finset.sum_congr rfl
      intro alpha _
      by_cases hlow : alpha.Nonempty ∧ alpha.card ≤ k
      · simp_rw [if_pos hlow]
        rw [finiteAverage_const_mul]
      · simp_rw [if_neg hlow]
        exact
          FiniteBooleanPerVertexRestrictionBound.finiteAverage_const 0
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro alpha _
      by_cases hlow : alpha.Nonempty ∧ alpha.card ≤ k
      · rw [if_pos hlow,
          finiteAverage_restrictedCharacter_eq_zero_of_patternUnbiased
            D T hD alpha hlow.2 hlow.1]
        ring
      · simp [hlow]

/-! ## Generic exact one-round expectation identity -/

/-- Averaging the pointwise Fourier trichotomy first over the live uniform
fill and then over the independent base/mask seed leaves only the uniform
constant and the signed high-degree tail. -/
theorem oneRoundAverage_eq_uniformAverage_add_highDegreeAverage
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased k D) :
    finiteAverage (fun seed : DSeed × TSeed =>
      finiteAverage (fun uniform : Fin n → Bool =>
        f (maskedInput (D seed.1) (T seed.2) uniform))) =
      finiteAverage f +
        finiteAverage (fun seed : DSeed × TSeed =>
          finiteAverage (fun uniform : Fin n → Bool =>
            ratHighDegreeFourierTail f k
              (maskedInput (D seed.1) (T seed.2) uniform))) := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          f (maskedInput (D seed.1) (T seed.2) uniform))) =
        finiteAverage (fun seed : DSeed × TSeed =>
          finiteAverage (fun uniform : Fin n → Bool =>
            coefficient f ∅ +
              ratLowDegreeNonemptyFourierPart f k
                (maskedInput (D seed.1) (T seed.2) uniform) +
              ratHighDegreeFourierTail f k
                (maskedInput (D seed.1) (T seed.2) uniform))) := by
      apply finiteAverage_congr
      intro seed
      apply finiteAverage_congr
      intro uniform
      exact fourier_inversion_eq_constant_add_lowDegreeNonempty_add_highDegree
        f (maskedInput (D seed.1) (T seed.2) uniform)
    _ = coefficient f ∅ +
          finiteAverage (fun seed : DSeed × TSeed =>
            finiteAverage (fun uniform : Fin n → Bool =>
              ratLowDegreeNonemptyFourierPart f k
                (maskedInput (D seed.1) (T seed.2) uniform))) +
          finiteAverage (fun seed : DSeed × TSeed =>
            finiteAverage (fun uniform : Fin n → Bool =>
              ratHighDegreeFourierTail f k
                (maskedInput (D seed.1) (T seed.2) uniform))) := by
      simp_rw [finiteAverage_add]
      simp only [FiniteBooleanPerVertexRestrictionBound.finiteAverage_const]
    _ = finiteAverage f +
          finiteAverage (fun seed : DSeed × TSeed =>
            finiteAverage (fun uniform : Fin n → Bool =>
              ratHighDegreeFourierTail f k
                (maskedInput (D seed.1) (T seed.2) uniform))) := by
      rw [ratLowDegreeNonemptyFourierPart_oneRoundAverage_eq_zero f D T hD,
        coefficient_empty_eq_finiteAverage]
      ring

end FiniteBooleanOneRoundFoolingBound

namespace FiniteUnambiguousFBDD

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanOneRoundFoolingBound

/-! ## Full one-round uFBDD bound -/

/-- Full one-round acceptance-probability bound at cutoff `2 * m`.

The `4 * m`-wise unbiased base law simultaneously cancels every nonempty
degree-`≤ 2 * m` character and supplies the pairwise character orthogonality
needed for the high-tail moment estimate.  The `2 * m`-wise false-biased mask
law supplies exact survival probability `p ^ (2 * m)`. -/
theorem ratAcceptanceIndicator_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : ∀ input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp : 0 ≤ p)
    (hD : IsKWisePatternUnbiased (4 * m) D)
    (hT : IsKWisePatternFalseBiased (2 * m) p T) :
    |finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          B.ratAcceptanceIndicator
            (maskedInput (D seed.1) (T seed.2) uniform))) -
      finiteAverage B.ratAcceptanceIndicator| ≤
      (Fintype.card B.Vertex : ℚ) * p ^ m := by
  have hDegree : 2 * m ≤ 4 * m := by omega
  have hDLow : IsKWisePatternUnbiased (2 * m) D := by
    intro support hsupport pattern
    exact hD support (le_trans hsupport hDegree) pattern
  have hDHigh : IsKWisePatternUnbiased (2 * (2 * m)) D := by
    simpa only [show 2 * (2 * m) = 4 * m by omega] using hD
  have hexact :=
    oneRoundAverage_eq_uniformAverage_add_highDegreeAverage
      B.ratAcceptanceIndicator D T hDLow
  have hgap :
      finiteAverage (fun seed : DSeed × TSeed =>
          finiteAverage (fun uniform : Fin n → Bool =>
            B.ratAcceptanceIndicator
              (maskedInput (D seed.1) (T seed.2) uniform))) -
        finiteAverage B.ratAcceptanceIndicator =
      finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail B.ratAcceptanceIndicator (2 * m)
            (maskedInput (D seed.1) (T seed.2) uniform))) := by
    rw [hexact]
    ring
  rw [hgap]
  calc
    |finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail B.ratAcceptanceIndicator (2 * m)
            (maskedInput (D seed.1) (T seed.2) uniform)))| ≤
        finiteAverage (fun seed : DSeed × TSeed =>
          |finiteAverage (fun uniform : Fin n → Bool =>
            ratHighDegreeFourierTail B.ratAcceptanceIndicator (2 * m)
              (maskedInput (D seed.1) (T seed.2) uniform))|) :=
      abs_finiteAverage_le_finiteAverage_abs _
    _ ≤ (Fintype.card B.Vertex : ℚ) * p ^ m :=
      B.ratHighDegreeFourierTail_maskedAverage_evenDegree_absMoment_le_card_mul_pow
        hreadOnce hunambiguous hreadsAll D T p hp
          (hDOrthogonal_of_twoKWisePatternUnbiased D hDHigh)
          (hTMask_of_kWisePatternFalseBiased T p hT)

end FiniteUnambiguousFBDD

/-! ## Mandatory canonical specialization -/

open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence

/-- The full one-round acceptance-probability estimate for the mandatory
canonical uFBDD.  This is deliberately a single-round statement. -/
theorem mandatoryCanonicalUFBDD_ratAcceptanceIndicator_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n timeSteps blockSize m : Nat) (hblockSize : 0 < blockSize)
    {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp : 0 ≤ p)
    (hD : IsKWisePatternUnbiased (4 * m) D)
    (hT : IsKWisePatternFalseBiased (2 * m) p T) :
    |finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          (mandatoryCanonicalUFBDD machine n timeSteps blockSize).ratAcceptanceIndicator
            (maskedInput (D seed.1) (T seed.2) uniform))) -
      finiteAverage
        (mandatoryCanonicalUFBDD machine n timeSteps blockSize).ratAcceptanceIndicator| ≤
      (Fintype.card
        (mandatoryCanonicalUFBDD machine n timeSteps blockSize).Vertex : ℚ) *
        p ^ m := by
  apply
    FiniteUnambiguousFBDD.ratAcceptanceIndicator_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce
      machine n timeSteps blockSize
  · exact mandatoryCanonicalUFBDD_isUnambiguous
      machine n timeSteps blockSize hblockSize
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
      machine n timeSteps blockSize currentInput path
  · exact hp
  · exact hD
  · exact hT

end OneTapeMagnification
end Frontier
end Pnp4
