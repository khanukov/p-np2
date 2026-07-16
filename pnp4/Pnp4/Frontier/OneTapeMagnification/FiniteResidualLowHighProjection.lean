import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilyResidualModelMass
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredWeightedCharge
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredPointMassCliqueObstruction

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Low--high projection for residual restriction mass

The conditional low-degree predictor is an orthogonal projection only when
the base source separates every high Fourier support from every low Fourier
support which is still present after restriction.  Bounded independence does
not supply that statement: a high/low symmetric difference can lie beyond its
independence budget.

This file records the exact cross term.  For the structured finite-field base
source it is supported precisely on high/low pairs whose symmetric difference
lies in the structured dual code.  Consequently the hoped-for projection
identity follows from an explicit no-alias premise, but not from
`(4m+1)`-wise unbiasedness alone.

The last section packages the elementary finite Schur bound used for a
dimension-`d` quotient class: a nonnegative symmetric kernel bounded by
`p^3` contributes at most `2^d * p^3 / 4` when its coefficient energy is at
most `1/4`.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanOneRoundFoolingBound
open FiniteBooleanPerVertexRestrictionBound
open FiniteUnambiguousFBDD
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open DPTWStructuredFullFieldCorrelation
open DPTWStructuredWeightedCharge
open DPTWStructuredPointMassCliqueObstruction

namespace FiniteBooleanResidualMass

local instance residualProjectionDualSupportDecidable
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    Decidable (IsStructuredDualSupport n k hn support) :=
  Classical.propDecidable _

/-! ## Exact low--high cross -/

/-- The low-degree conditional predictor is the corresponding sum of
restricted-character averages. -/
theorem maskedLowDegreePredictor_eq_sum_restrictedCharacters
    {n : Nat} (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    maskedLowDegreePredictor f cutoff base mask =
      ∑ support ∈ lowDegreeSupports n cutoff,
        coefficient f support *
          restrictedCharacterAverage support base mask := by
  unfold maskedLowDegreePredictor ratLowDegreeFourierPart
  rw [finiteAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro support _
  rw [finiteAverage_const_mul]
  rfl

/-- Exact Fourier expression for the cross between the strict high tail and
the conditional low-degree predictor. -/
noncomputable def lowHighRestrictionCrossCorrelation
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) : Rat :=
  ∑ high ∈ highDegreeSupports n cutoff,
    ∑ low ∈ lowDegreeSupports n cutoff,
      coefficient f high * coefficient f low *
        finiteAverage (fun seed : DSeed × TSeed =>
          restrictedCharacterAverage high (D seed.1) (T seed.2) *
            restrictedCharacterAverage low (D seed.1) (T seed.2))

/-- Expanding both conditional Fourier pieces gives the exact low--high
cross, with no independence assumption. -/
theorem highTailAverage_mul_maskedLowDegreePredictor_eq_crossCorrelation
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      finiteAverage (fun uniform : Fin n -> Bool =>
        ratHighDegreeFourierTail f cutoff
          (maskedInput (D seed.1) (T seed.2) uniform)) *
      maskedLowDegreePredictor f cutoff
        (D seed.1) (T seed.2)) =
      lowHighRestrictionCrossCorrelation f cutoff D T := by
  classical
  let highSupports := highDegreeSupports n cutoff
  let lowSupports := lowDegreeSupports n cutoff
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n -> Bool =>
          ratHighDegreeFourierTail f cutoff
            (maskedInput (D seed.1) (T seed.2) uniform)) *
        maskedLowDegreePredictor f cutoff
          (D seed.1) (T seed.2)) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (∑ high ∈ highSupports,
          coefficient f high *
            restrictedCharacterAverage high (D seed.1) (T seed.2)) *
        (∑ low ∈ lowSupports,
          coefficient f low *
            restrictedCharacterAverage low (D seed.1) (T seed.2))) := by
          apply finiteAverage_congr
          intro seed
          rw [finiteAverage_ratHighDegreeFourierTail_masked,
            maskedLowDegreePredictor_eq_sum_restrictedCharacters]
    _ = finiteAverage (fun seed : DSeed × TSeed =>
        ∑ high ∈ highSupports, ∑ low ∈ lowSupports,
          (coefficient f high *
              restrictedCharacterAverage high (D seed.1) (T seed.2)) *
            (coefficient f low *
              restrictedCharacterAverage low (D seed.1) (T seed.2))) := by
          apply finiteAverage_congr
          intro seed
          rw [Finset.sum_mul_sum]
    _ = ∑ high ∈ highSupports, ∑ low ∈ lowSupports,
        finiteAverage (fun seed : DSeed × TSeed =>
          (coefficient f high *
              restrictedCharacterAverage high (D seed.1) (T seed.2)) *
            (coefficient f low *
              restrictedCharacterAverage low (D seed.1) (T seed.2))) := by
          rw [finiteAverage_finset_sum]
          apply Finset.sum_congr rfl
          intro high _
          rw [finiteAverage_finset_sum]
    _ = lowHighRestrictionCrossCorrelation f cutoff D T := by
          unfold lowHighRestrictionCrossCorrelation
          apply Finset.sum_congr rfl
          intro high _
          apply Finset.sum_congr rfl
          intro low _
          calc
            finiteAverage (fun seed : DSeed × TSeed =>
                (coefficient f high *
                    restrictedCharacterAverage high
                      (D seed.1) (T seed.2)) *
                  (coefficient f low *
                    restrictedCharacterAverage low
                      (D seed.1) (T seed.2))) =
              finiteAverage (fun seed : DSeed × TSeed =>
                (coefficient f high * coefficient f low) *
                  (restrictedCharacterAverage high
                      (D seed.1) (T seed.2) *
                    restrictedCharacterAverage low
                      (D seed.1) (T seed.2))) := by
                        apply finiteAverage_congr
                        intro seed
                        ring
            _ = _ := finiteAverage_const_mul _ _

/-- The cross factors into a base-character correlation and a mask-survival
probability.  This is the exact formula showing why bounded independence can
miss high/low aliases. -/
theorem lowHighRestrictionCrossCorrelation_eq_characterMaskSum
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    lowHighRestrictionCrossCorrelation f cutoff D T =
      ∑ high ∈ highDegreeSupports n cutoff,
        ∑ low ∈ lowDegreeSupports n cutoff,
          coefficient f high * coefficient f low *
            (finiteAverage (fun d : DSeed =>
                character (high ∆ low) (D d)) *
              finiteAverage (fun t : TSeed =>
                maskAllZeroIndicator (high ∪ low) (T t))) := by
  classical
  unfold lowHighRestrictionCrossCorrelation
  apply Finset.sum_congr rfl
  intro high _
  apply Finset.sum_congr rfl
  intro low _
  rw [restrictedCharacterAverage_pairMoment_eq D T high low]

/-! ## A Boolean-valued high/low alias witness -/

/-- The rational `{0,1}` function `(1 + chi_support) / 2`. -/
def halfOneAddCharacter {n : Nat} (support : Finset (Fin n))
    (input : Fin n -> Bool) : Rat :=
  (1 + character support input) / 2

/-- Its Fourier spectrum consists only of the constant character and the
displayed support (with the expected collision when the support is empty). -/
theorem coefficient_halfOneAddCharacter
    {n : Nat} (support test : Finset (Fin n)) :
    coefficient (halfOneAddCharacter support) test =
      (if test = ∅ then (1 : Rat) / 2 else 0) +
        (if support = test then (1 : Rat) / 2 else 0) := by
  rw [FiniteBooleanFourierEnergy.coefficient_eq_finiteAverage_mul]
  unfold halfOneAddCharacter
  calc
    finiteAverage (fun input : Fin n -> Bool =>
        (1 + character support input) / 2 * character test input) =
      finiteAverage (fun input : Fin n -> Bool =>
        ((1 : Rat) / 2) *
            (character ∅ input * character test input) +
          ((1 : Rat) / 2) *
            (character support input * character test input)) := by
              apply finiteAverage_congr
              intro input
              simp
              ring
    _ = ((1 : Rat) / 2) *
          finiteAverage (fun input : Fin n -> Bool =>
            character ∅ input * character test input) +
        ((1 : Rat) / 2) *
          finiteAverage (fun input : Fin n -> Bool =>
            character support input * character test input) := by
              rw [finiteAverage_add, finiteAverage_const_mul,
                finiteAverage_const_mul]
    _ = _ := by
      rw [FiniteBooleanFourierEnergy.finiteAverage_character_mul_character,
        FiniteBooleanFourierEnergy.finiteAverage_character_mul_character]
      by_cases htest : test = ∅
      · subst test
        simp
      · have hemptyNe : ∅ ≠ test := Ne.symm htest
        by_cases hsupport : support = test <;>
          simp [htest, hemptyNe, hsupport]

/-- If the displayed support is strictly above the cutoff, the entire
low--high cross of `(1 + chi_support)/2` is one quarter of its single
restricted-character alias with the constant term. -/
theorem lowHighRestrictionCrossCorrelation_halfOneAddCharacter_eq
    {n cutoff : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (support : Finset (Fin n)) (hhigh : cutoff < support.card)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    lowHighRestrictionCrossCorrelation
        (halfOneAddCharacter support) cutoff D T =
      (1 : Rat) / 4 *
        finiteAverage (fun seed : DSeed × TSeed =>
          restrictedCharacterAverage support (D seed.1) (T seed.2) *
            restrictedCharacterAverage ∅ (D seed.1) (T seed.2)) := by
  classical
  have hsupportNonempty : support ≠ ∅ := by
    intro hempty
    subst support
    simp at hhigh
  unfold lowHighRestrictionCrossCorrelation
  calc
    (∑ high ∈ highDegreeSupports n cutoff,
        ∑ low ∈ lowDegreeSupports n cutoff,
          coefficient (halfOneAddCharacter support) high *
            coefficient (halfOneAddCharacter support) low *
              finiteAverage (fun seed : DSeed × TSeed =>
                restrictedCharacterAverage high (D seed.1) (T seed.2) *
                  restrictedCharacterAverage low (D seed.1) (T seed.2))) =
      ∑ low ∈ lowDegreeSupports n cutoff,
        coefficient (halfOneAddCharacter support) support *
          coefficient (halfOneAddCharacter support) low *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage support (D seed.1) (T seed.2) *
                restrictedCharacterAverage low (D seed.1) (T seed.2)) := by
          apply Finset.sum_eq_single support
          · intro high hhighMem hhighNe
            have hhighCard := mem_highDegreeSupports.mp hhighMem
            have hhighNonempty : high ≠ ∅ := by
              intro hempty
              subst high
              simp at hhighCard
            have hsupportNeHigh : support ≠ high := Ne.symm hhighNe
            rw [coefficient_halfOneAddCharacter support high]
            simp [hhighNonempty, hsupportNeHigh]
          · intro hnotMem
            exact False.elim
              (hnotMem (mem_highDegreeSupports.mpr hhigh))
    _ = coefficient (halfOneAddCharacter support) support *
          coefficient (halfOneAddCharacter support) ∅ *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage support (D seed.1) (T seed.2) *
                restrictedCharacterAverage ∅ (D seed.1) (T seed.2)) := by
          apply Finset.sum_eq_single ∅
          · intro low hlowMem hlowNe
            have hlowCard := mem_lowDegreeSupports.mp hlowMem
            have hsupportNeLow : support ≠ low := by
              intro heq
              subst low
              omega
            rw [coefficient_halfOneAddCharacter support low]
            simp [hlowNe, hsupportNeLow]
          · intro hnotMem
            exact False.elim
              (hnotMem (mem_lowDegreeSupports.mpr (by simp)))
    _ = _ := by
      have hcoeffSupport :
          coefficient (halfOneAddCharacter support) support =
            (1 : Rat) / 2 := by
        rw [coefficient_halfOneAddCharacter support support]
        simp [hsupportNonempty]
      have hcoeffEmpty :
          coefficient (halfOneAddCharacter support) ∅ =
            (1 : Rat) / 2 := by
        rw [coefficient_halfOneAddCharacter support ∅]
        simp [hsupportNonempty]
      rw [hcoeffSupport, hcoeffEmpty]
      ring

/-- A structured dual word above the cutoff is an explicit surviving
high/low alias for a Boolean-valued function. -/
theorem structured_lowHighRestrictionCrossCorrelation_halfOneAddCharacter_eq
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) (hhigh : cutoff < support.card)
    (hdual : IsStructuredDualSupport n (structuredIndependence m) hn support) :
    lowHighRestrictionCrossCorrelation
        (halfOneAddCharacter support) cutoff
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate =
      (1 : Rat) / 4 *
        finiteAverage
          (fun t : Fin (structuredIndependence m * n) -> Bool =>
            maskAllZeroIndicator support
              ((structuredDyadicPrimitive n m tailBits hn htail).generate t)) := by
  rw [lowHighRestrictionCrossCorrelation_halfOneAddCharacter_eq
    support hhigh]
  have hpair :=
    structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq
      n m hn
      (structuredDyadicPrimitive n m tailBits hn htail).generate
      support ∅
  have hdiff : support ∆ ∅ = support := by
    ext index
    simp [Finset.mem_symmDiff]
  have hunion : support ∪ ∅ = support := by simp
  rw [hdiff, hunion, if_pos hdual] at hpair
  simp at hpair
  rw [hpair]

/-- Fully concrete failure of low--high projection on the structured source.
At `n = 2`, `m = 0`, and cutoff zero, the two-point support `support01` is a
degree-one dual word.  Under the full two-coordinate mask it survives with
probability `1/4`, so its Boolean alias witness has cross exactly `1/16`. -/
theorem structured_lowHighRestrictionCrossCorrelation_support01_eq_one_div_sixteen :
    lowHighRestrictionCrossCorrelation
        (halfOneAddCharacter support01) 0
        (structuredUnbiasedPrimitive 2 0 (by omega)).generate
        (structuredDyadicPrimitive 2 0 2 (by omega)
          (Nat.le_refl 2)).generate =
      (1 : Rat) / 16 := by
  have hsupportCard : support01.card = 2 := by
    decide
  have hdual :
      IsStructuredDualSupport 2 (structuredIndependence 0) (by omega)
        support01 := by
    exact isStructuredDualSupport_degreeOne_of_even_card
      2 (by omega) support01 (by decide)
  have hbudget : structuredIndependence 0 ≤ support01.card := by
    simp [structuredIndependence, hsupportCard]
  rw [structured_lowHighRestrictionCrossCorrelation_halfOneAddCharacter_eq
    2 0 2 0 (by omega) (Nat.le_refl 2) support01 (by omega) hdual]
  rw [structuredDyadicPrimitive_fullMaskSurvival_exact
    2 0 (by omega) support01 hbudget]
  norm_num [structuredIndependence]

/-- For the actual structured base source, the cross is supported exactly on
high/low pairs whose symmetric difference is a structured dual-code word. -/
theorem structured_lowHighRestrictionCrossCorrelation_eq_dualAliases
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    lowHighRestrictionCrossCorrelation f cutoff
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate =
      ∑ high ∈ highDegreeSupports (2 ^ n) cutoff,
        ∑ low ∈ lowDegreeSupports (2 ^ n) cutoff,
          if IsStructuredDualSupport n (structuredIndependence m) hn
              (high ∆ low) then
            coefficient f high * coefficient f low *
              finiteAverage
                (fun t : Fin (structuredIndependence m * n) -> Bool =>
                  maskAllZeroIndicator (high ∪ low)
                    ((structuredDyadicPrimitive n m tailBits hn htail).generate t))
          else 0 := by
  classical
  unfold lowHighRestrictionCrossCorrelation
  apply Finset.sum_congr rfl
  intro high _
  apply Finset.sum_congr rfl
  intro low _
  rw [structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq]
  by_cases hdual : IsStructuredDualSupport n
      (structuredIndependence m) hn (high ∆ low)
  · simp [hdual]
  · simp [hdual]

/-- A supported symmetric-difference bound turns `q`-wise unbiasedness into
the missing cross orthogonality.  Without this extra support premise, high
supports can be arbitrarily far from the low projection. -/
theorem lowHighRestrictionCrossCorrelation_eq_zero_of_supportedSymmDiff_le
    {n cutoff q : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (hD : IsKWisePatternUnbiased q D)
    (hsupported : ∀ high ∈ highDegreeSupports n cutoff,
      ∀ low ∈ lowDegreeSupports n cutoff,
        coefficient f high * coefficient f low ≠ 0 ->
          (high ∆ low).card ≤ q) :
    lowHighRestrictionCrossCorrelation f cutoff D T = 0 := by
  classical
  rw [lowHighRestrictionCrossCorrelation_eq_characterMaskSum]
  apply Finset.sum_eq_zero
  intro high hhigh
  apply Finset.sum_eq_zero
  intro low hlow
  by_cases hcoefficient : coefficient f high * coefficient f low = 0
  · simp [hcoefficient]
  · have hne : high ≠ low := by
      intro heq
      subst low
      have hhighCard := mem_highDegreeSupports.mp hhigh
      have hlowCard := mem_lowDegreeSupports.mp hlow
      omega
    have hzero :
        finiteAverage (fun d : DSeed => character (high ∆ low) (D d)) = 0 :=
      character_pair_average_eq_zero_of_patternUnbiased
        D hD high low hne (hsupported high hhigh low hlow hcoefficient)
    rw [hzero]
    ring

/-- Full pattern-unbiasedness is the unconditional orthogonal-projection
regime, for an arbitrary independent mask source. -/
theorem lowHighRestrictionCrossCorrelation_eq_zero_of_fullPatternUnbiased
    {n cutoff : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (hD : IsKWisePatternUnbiased n D) :
    lowHighRestrictionCrossCorrelation f cutoff D T = 0 := by
  apply lowHighRestrictionCrossCorrelation_eq_zero_of_supportedSymmDiff_le
      f D T hD
  intro high _ low _ _
  calc
    (high ∆ low).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    _ = n := Fintype.card_fin n

/-- On the structured source, absence of Fourier-supported high/low dual
aliases is a sufficient and exact-to-check projection criterion. -/
theorem structured_lowHighRestrictionCrossCorrelation_eq_zero_of_noDualAlias
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hnoAlias : ∀ high ∈ highDegreeSupports (2 ^ n) cutoff,
      ∀ low ∈ lowDegreeSupports (2 ^ n) cutoff,
        coefficient f high * coefficient f low ≠ 0 ->
          ¬ IsStructuredDualSupport n (structuredIndependence m) hn
            (high ∆ low)) :
    lowHighRestrictionCrossCorrelation f cutoff
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate = 0 := by
  classical
  rw [structured_lowHighRestrictionCrossCorrelation_eq_dualAliases]
  apply Finset.sum_eq_zero
  intro high hhigh
  apply Finset.sum_eq_zero
  intro low hlow
  by_cases hcoefficient : coefficient f high * coefficient f low = 0
  · simp [hcoefficient]
  · simp [hnoAlias high hhigh low hlow hcoefficient]

/-! ## Exact Pythagorean correction -/

/-- The desired identity `E[A P] = E[P^2]` has exactly one correction: the
low--high cross above. -/
theorem maskedAverage_mul_predictor_eq_predictorSq_add_cross
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      maskedAverage f (D seed.1) (T seed.2) *
        maskedLowDegreePredictor f cutoff (D seed.1) (T seed.2)) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (maskedLowDegreePredictor f cutoff
          (D seed.1) (T seed.2)) ^ 2) +
        lowHighRestrictionCrossCorrelation f cutoff D T := by
  have hcross :=
    highTailAverage_mul_maskedLowDegreePredictor_eq_crossCorrelation
      f cutoff D T
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        maskedAverage f (D seed.1) (T seed.2) *
          maskedLowDegreePredictor f cutoff (D seed.1) (T seed.2)) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (maskedAverage f (D seed.1) (T seed.2) -
            maskedLowDegreePredictor f cutoff (D seed.1) (T seed.2)) *
          maskedLowDegreePredictor f cutoff (D seed.1) (T seed.2) +
        (maskedLowDegreePredictor f cutoff
          (D seed.1) (T seed.2)) ^ 2) := by
            apply finiteAverage_congr
            intro seed
            ring
    _ = finiteAverage (fun seed : DSeed × TSeed =>
          (maskedAverage f (D seed.1) (T seed.2) -
              maskedLowDegreePredictor f cutoff (D seed.1) (T seed.2)) *
            maskedLowDegreePredictor f cutoff (D seed.1) (T seed.2)) +
        finiteAverage (fun seed : DSeed × TSeed =>
          (maskedLowDegreePredictor f cutoff
            (D seed.1) (T seed.2)) ^ 2) := by
              rw [finiteAverage_add]
    _ = lowHighRestrictionCrossCorrelation f cutoff D T +
        finiteAverage (fun seed : DSeed × TSeed =>
          (maskedLowDegreePredictor f cutoff
            (D seed.1) (T seed.2)) ^ 2) := by
          rw [← hcross]
          apply congrArg (fun value => value + finiteAverage (fun seed : DSeed × TSeed =>
            (maskedLowDegreePredictor f cutoff
              (D seed.1) (T seed.2)) ^ 2))
          apply finiteAverage_congr
          intro seed
          rw [highTailAverage_eq_maskedAverage_sub_lowDegreePredictor]
    _ = _ := by ring

/-- Corrected Pythagorean identity.  The hoped-for variance subtraction is
valid exactly when the cross correction vanishes. -/
theorem deviation_secondMoment_eq_averageSq_sub_predictorSq_sub_twoCross
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (maskedAverage f (D seed.1) (T seed.2) -
        maskedLowDegreePredictor f cutoff (D seed.1) (T seed.2)) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (maskedAverage f (D seed.1) (T seed.2)) ^ 2) -
      finiteAverage (fun seed : DSeed × TSeed =>
        (maskedLowDegreePredictor f cutoff
          (D seed.1) (T seed.2)) ^ 2) -
      2 * lowHighRestrictionCrossCorrelation f cutoff D T := by
  have hcross := maskedAverage_mul_predictor_eq_predictorSq_add_cross
    f cutoff D T
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        (maskedAverage f (D seed.1) (T seed.2) -
          maskedLowDegreePredictor f cutoff
            (D seed.1) (T seed.2)) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (maskedAverage f (D seed.1) (T seed.2)) ^ 2 -
          2 * (maskedAverage f (D seed.1) (T seed.2) *
            maskedLowDegreePredictor f cutoff
              (D seed.1) (T seed.2)) +
          (maskedLowDegreePredictor f cutoff
            (D seed.1) (T seed.2)) ^ 2) := by
              apply finiteAverage_congr
              intro seed
              ring
    _ = finiteAverage (fun seed : DSeed × TSeed =>
          (maskedAverage f (D seed.1) (T seed.2)) ^ 2) -
        2 * finiteAverage (fun seed : DSeed × TSeed =>
          maskedAverage f (D seed.1) (T seed.2) *
            maskedLowDegreePredictor f cutoff
              (D seed.1) (T seed.2)) +
        finiteAverage (fun seed : DSeed × TSeed =>
          (maskedLowDegreePredictor f cutoff
            (D seed.1) (T seed.2)) ^ 2) := by
              rw [finiteAverage_add, finiteAverage_sub,
                finiteAverage_const_mul]
    _ = _ := by rw [hcross]; ring

/-- Under genuine low--high orthogonality, the residual deviation has no more
second moment than the raw residual mass. -/
theorem deviation_secondMoment_le_maskedAverage_secondMoment_of_cross_eq_zero
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n -> Bool) -> Rat) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (hcross : lowHighRestrictionCrossCorrelation f cutoff D T = 0) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (maskedAverage f (D seed.1) (T seed.2) -
        maskedLowDegreePredictor f cutoff (D seed.1) (T seed.2)) ^ 2) ≤
      finiteAverage (fun seed : DSeed × TSeed =>
        (maskedAverage f (D seed.1) (T seed.2)) ^ 2) := by
  rw [deviation_secondMoment_eq_averageSq_sub_predictorSq_sub_twoCross,
    hcross]
  have hpredictorNonnegative :
      0 ≤ finiteAverage (fun seed : DSeed × TSeed =>
        (maskedLowDegreePredictor f cutoff
          (D seed.1) (T seed.2)) ^ 2) :=
    finiteAverage_nonneg fun seed => sq_nonneg _
  linarith

end FiniteBooleanResidualMass

namespace FiniteResidualQuotientCharge

/-! ## Abstract quotient-class bound -/

/-- A nonnegative symmetric kernel with entrywise bound `entryBound` has
quadratic charge at most `card * entryBound` times coefficient energy. -/
theorem signedQuadraticSum_le_card_mul_entryBound_mul_energy
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (c : Index -> Rat)
    (kernel : Index -> Index -> Rat) (entryBound : Rat)
    (hkernelNonnegative : ∀ left ∈ indices, ∀ right ∈ indices,
      0 ≤ kernel left right)
    (hkernelSymmetric : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right = kernel right left)
    (hkernelBound : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right ≤ entryBound) :
    signedQuadraticSum indices c kernel ≤
      (indices.card : Rat) * entryBound *
        ∑ index ∈ indices, c index ^ 2 := by
  apply signedQuadraticSum_le_budget_mul_energy
      indices c (fun _ => 1) kernel ((indices.card : Rat) * entryBound)
  · intro index _
    norm_num
  · exact hkernelNonnegative
  · exact hkernelSymmetric
  · intro left hleft
    unfold weightedRowCharge
    simp only [mul_one]
    calc
      (∑ right ∈ indices, kernel left right) ≤
          ∑ _right ∈ indices, entryBound := by
            apply Finset.sum_le_sum
            intro right hright
            exact hkernelBound left hleft right hright
      _ = (indices.card : Rat) * entryBound := by simp

/-- If the quotient has at most `2^d` supports and energy at most `1/4`, the
preceding bound becomes `2^d * entryBound / 4`. -/
theorem signedQuadraticSum_le_pow_mul_entryBound_div_four
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (c : Index -> Rat)
    (kernel : Index -> Index -> Rat) (entryBound : Rat) (d : Nat)
    (hentryNonnegative : 0 ≤ entryBound)
    (hkernelNonnegative : ∀ left ∈ indices, ∀ right ∈ indices,
      0 ≤ kernel left right)
    (hkernelSymmetric : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right = kernel right left)
    (hkernelBound : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right ≤ entryBound)
    (hcard : indices.card ≤ 2 ^ d)
    (henergy : (∑ index ∈ indices, c index ^ 2) ≤ (1 : Rat) / 4) :
    signedQuadraticSum indices c kernel ≤
      (2 : Rat) ^ d * entryBound / 4 := by
  have hcharge := signedQuadraticSum_le_card_mul_entryBound_mul_energy
    indices c kernel entryBound hkernelNonnegative
      hkernelSymmetric hkernelBound
  have hcardRat : (indices.card : Rat) ≤ (2 : Rat) ^ d := by
    exact_mod_cast hcard
  have henergyNonnegative :
      0 ≤ ∑ index ∈ indices, c index ^ 2 := by positivity
  calc
    signedQuadraticSum indices c kernel ≤
        (indices.card : Rat) * entryBound *
          ∑ index ∈ indices, c index ^ 2 := hcharge
    _ ≤ (2 : Rat) ^ d * entryBound *
          ∑ index ∈ indices, c index ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcardRat hentryNonnegative)
              henergyNonnegative
    _ ≤ (2 : Rat) ^ d * entryBound * ((1 : Rat) / 4) := by
            exact mul_le_mul_of_nonneg_left henergy
              (mul_nonneg (by positivity) hentryNonnegative)
    _ = (2 : Rat) ^ d * entryBound / 4 := by ring

/-- The form used by the quotient search: an entry bound `p^3` yields
`Q ≤ 2^d p^3 / 4`. -/
theorem signedQuadraticSum_le_pow_mul_pow_three_div_four
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (c : Index -> Rat)
    (kernel : Index -> Index -> Rat) (p : Rat) (d : Nat)
    (hp : 0 ≤ p)
    (hkernelNonnegative : ∀ left ∈ indices, ∀ right ∈ indices,
      0 ≤ kernel left right)
    (hkernelSymmetric : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right = kernel right left)
    (hkernelBound : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right ≤ p ^ 3)
    (hcard : indices.card ≤ 2 ^ d)
    (henergy : (∑ index ∈ indices, c index ^ 2) ≤ (1 : Rat) / 4) :
    signedQuadraticSum indices c kernel ≤
      (2 : Rat) ^ d * p ^ 3 / 4 := by
  simpa only [mul_assoc] using
    (signedQuadraticSum_le_pow_mul_entryBound_div_four
      indices c kernel (p ^ 3) d (pow_nonneg hp 3)
      hkernelNonnegative hkernelSymmetric hkernelBound hcard henergy)

/-- Safe quotient-dimension range for the dyadic false probability
`p = 2^{-tailBits}`.  The abstract quotient bound
`2^d * p^3 / 4` is at most `p^2` whenever `d ≤ tailBits + 2`.

This theorem remains purely conditional on the displayed kernel, cardinality,
and energy premises; it does not assert that an actual selector supplies
them. -/
theorem signedQuadraticSum_le_inversePow_square_of_dimension_le
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (c : Index -> Rat)
    (kernel : Index -> Index -> Rat) (tailBits d : Nat)
    (hkernelNonnegative : ∀ left ∈ indices, ∀ right ∈ indices,
      0 ≤ kernel left right)
    (hkernelSymmetric : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right = kernel right left)
    (hkernelBound : ∀ left ∈ indices, ∀ right ∈ indices,
      kernel left right ≤ ((1 : Rat) / (2 : Rat) ^ tailBits) ^ 3)
    (hcard : indices.card ≤ 2 ^ d)
    (henergy : (∑ index ∈ indices, c index ^ 2) ≤ (1 : Rat) / 4)
    (hdimension : d ≤ tailBits + 2) :
    signedQuadraticSum indices c kernel ≤
      ((1 : Rat) / (2 : Rat) ^ tailBits) ^ 2 := by
  let p : Rat := (1 : Rat) / (2 : Rat) ^ tailBits
  have hp : 0 ≤ p := by
    dsimp only [p]
    positivity
  have hquotient :
      signedQuadraticSum indices c kernel ≤
        (2 : Rat) ^ d * p ^ 3 / 4 := by
    apply signedQuadraticSum_le_pow_mul_pow_three_div_four
      indices c kernel p d hp hkernelNonnegative hkernelSymmetric
    · simpa only [p] using hkernelBound
    · exact hcard
    · exact henergy
  have hpower :
      (2 : Rat) ^ d ≤ (2 : Rat) ^ (tailBits + 2) :=
    pow_le_pow_right₀ (by norm_num) hdimension
  have hpThree : 0 ≤ p ^ 3 := pow_nonneg hp 3
  calc
    signedQuadraticSum indices c kernel ≤
        (2 : Rat) ^ d * p ^ 3 / 4 := hquotient
    _ ≤ (2 : Rat) ^ (tailBits + 2) * p ^ 3 / 4 := by
          have hmultiply := mul_le_mul_of_nonneg_right hpower hpThree
          linarith
    _ = ((1 : Rat) / (2 : Rat) ^ tailBits) ^ 2 := by
      dsimp only [p]
      rw [pow_add]
      have hpowNe : (2 : Rat) ^ tailBits ≠ 0 := by positivity
      norm_num
      field_simp [hpowNe]
      ring

end FiniteResidualQuotientCharge

end

end OneTapeMagnification
end Frontier
end Pnp4
