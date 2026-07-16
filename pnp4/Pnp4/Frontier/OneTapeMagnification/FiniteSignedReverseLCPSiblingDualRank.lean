import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPFourierKernel
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredRankWeightedDualCorrelation
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Structured dual-rank form of sibling-cone cross terms

Cross-inner-products between extended child cones are one component of a
reverse-LCP square drop.  This file exposes an arbitrary such bilinear cross
moment as an exact structured dual-code form, then splits it into the
same-support diagonal and the distinct dual-alias residual.  It does not
assert that the two steps are distinct realized children, nor that these
cross terms exhaust a local drop: traces terminating at the parent key can
also contribute boundary terms.  The mask weight remains the inverse power
of the actual union-support constraint rank.

For distinct dual aliases, the structured code distance and mask
interpolation give the unconditional rank lower bound

```text
(4m + 1) * tailBits <= rank(left union right).
```

The final cone lemma retains the two suffix-cylinder character phases and
the reachable-prefix Fourier coefficients exactly.  No summation bound or
frame/Carleson inequality is asserted.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanOneRoundFoolingBound
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanBoundedIndependenceFarTail
open FiniteUnambiguousFBDD
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open MandatoryCanonicalSelectorPairCorrelation
open FiniteBooleanDualAliasConvolutionTransfer

namespace FiniteSignedReverseLCPSiblingDualRank

/-! ## Bilinear structured high-tail form -/

/-- Structured-seed inner product of the two masked conditional high tails. -/
noncomputable def structuredHighTailCrossMoment
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) : Rat :=
  finiteAverage (fun seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n) =>
    finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
      ratHighDegreeFourierTail leftFunction cutoff
        (maskedInput
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          uniform)) *
      finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        ratHighDegreeFourierTail rightFunction cutoff
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
            uniform)))

/-- Full bilinear dual-code form, including the same-support diagonal. -/
noncomputable def structuredDualRankCrossForm
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) : Rat := by
  classical
  exact
    ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
      ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
        if IsStructuredDualSupport n (structuredIndependence m) hn
            (left ∆ right) then
          coefficient leftFunction left * coefficient rightFunction right *
            (1 / (2 : Rat) ^
              supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail (left ∪ right))
        else 0

/-- Exact bilinear structured character calculation. -/
theorem structuredHighTailCrossMoment_eq_dualRankCrossForm
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredHighTailCrossMoment n m tailBits cutoff hn htail
        leftFunction rightFunction =
      structuredDualRankCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction := by
  classical
  unfold structuredHighTailCrossMoment structuredDualRankCrossForm
  calc
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
        ratHighDegreeFourierTail leftFunction cutoff
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
            uniform)) *
        finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
          ratHighDegreeFourierTail rightFunction cutoff
            (maskedInput
              ((structuredUnbiasedPrimitive n m hn).generate seed.1)
              ((structuredDyadicPrimitive n m tailBits hn htail).generate
                seed.2)
              uniform))) =
      finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        (∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
            coefficient leftFunction left *
              restrictedCharacterAverage left
                ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  seed.2)) *
          (∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
            coefficient rightFunction right *
              restrictedCharacterAverage right
                ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                ((structuredDyadicPrimitive n m tailBits hn htail).generate
                  seed.2))) := by
            apply finiteAverage_congr
            intro seed
            rw [finiteAverage_ratHighDegreeFourierTail_masked,
              finiteAverage_ratHighDegreeFourierTail_masked]
    _ = finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) =>
        ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
          ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
            (coefficient leftFunction left *
                restrictedCharacterAverage left
                  ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    seed.2)) *
              (coefficient rightFunction right *
                restrictedCharacterAverage right
                  ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                  ((structuredDyadicPrimitive n m tailBits hn htail).generate
                    seed.2))) := by
              apply finiteAverage_congr
              intro seed
              rw [Finset.sum_mul_sum]
    _ = ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
          ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
            finiteAverage (fun seed :
                FiniteBitTape (structuredIndependence m * n) ×
                  FiniteBitTape (structuredIndependence m * n) =>
              (coefficient leftFunction left *
                  restrictedCharacterAverage left
                    ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                    ((structuredDyadicPrimitive n m tailBits hn htail).generate
                      seed.2)) *
                (coefficient rightFunction right *
                  restrictedCharacterAverage right
                    ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                    ((structuredDyadicPrimitive n m tailBits hn htail).generate
                      seed.2))) := by
                rw [finiteAverage_finset_sum]
                apply Finset.sum_congr rfl
                intro left _
                rw [finiteAverage_finset_sum]
    _ = ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
          ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
            coefficient leftFunction left * coefficient rightFunction right *
              finiteAverage (fun seed :
                  FiniteBitTape (structuredIndependence m * n) ×
                    FiniteBitTape (structuredIndependence m * n) =>
                restrictedCharacterAverage left
                    ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                    ((structuredDyadicPrimitive n m tailBits hn htail).generate
                      seed.2) *
                  restrictedCharacterAverage right
                    ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                    ((structuredDyadicPrimitive n m tailBits hn htail).generate
                      seed.2)) := by
                apply Finset.sum_congr rfl
                intro left _
                apply Finset.sum_congr rfl
                intro right _
                calc
                  finiteAverage (fun seed :
                      FiniteBitTape (structuredIndependence m * n) ×
                        FiniteBitTape (structuredIndependence m * n) =>
                    (coefficient leftFunction left *
                        restrictedCharacterAverage left
                          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                          ((structuredDyadicPrimitive n m tailBits hn htail).generate
                            seed.2)) *
                      (coefficient rightFunction right *
                        restrictedCharacterAverage right
                          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                          ((structuredDyadicPrimitive n m tailBits hn htail).generate
                            seed.2))) =
                    finiteAverage (fun seed :
                        FiniteBitTape (structuredIndependence m * n) ×
                          FiniteBitTape (structuredIndependence m * n) =>
                      (coefficient leftFunction left *
                        coefficient rightFunction right) *
                        (restrictedCharacterAverage left
                            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                            ((structuredDyadicPrimitive n m tailBits hn htail).generate
                              seed.2) *
                          restrictedCharacterAverage right
                            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                            ((structuredDyadicPrimitive n m tailBits hn htail).generate
                              seed.2))) := by
                              apply finiteAverage_congr
                              intro seed
                              ring
                  _ = _ := finiteAverage_const_mul _ _
    _ = ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
          ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
            if IsStructuredDualSupport n (structuredIndependence m) hn
                (left ∆ right) then
              coefficient leftFunction left * coefficient rightFunction right *
                (1 / (2 : Rat) ^
                  supportPrefixConstraintRank n (structuredIndependence m)
                    tailBits hn htail (left ∪ right))
            else 0 := by
              apply Finset.sum_congr rfl
              intro left _
              apply Finset.sum_congr rfl
              intro right _
              rw [structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq]
              rw [structuredDyadicPrimitive_maskSurvival_eq_invPowRank]
              by_cases hdual : IsStructuredDualSupport n
                  (structuredIndependence m) hn (left ∆ right)
              · simp [hdual]
              · simp [hdual]

/-! ## Diagonal, distinct aliases, and unconditional rank -/

/-- Same-support part of the bilinear dual-rank form. -/
noncomputable def structuredDualRankDiagonalCrossForm
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) : Rat :=
  ∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
    coefficient leftFunction support * coefficient rightFunction support *
      (1 / (2 : Rat) ^
        supportPrefixConstraintRank n (structuredIndependence m)
          tailBits hn htail support)

/-- Distinct dual-alias part of the bilinear dual-rank form. -/
noncomputable def structuredDualRankDistinctCrossForm
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) : Rat := by
  classical
  exact
    ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
      ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
        if left ≠ right ∧
            IsStructuredDualSupport n (structuredIndependence m) hn
              (left ∆ right) then
          coefficient leftFunction left * coefficient rightFunction right *
            (1 / (2 : Rat) ^
              supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail (left ∪ right))
        else 0

/-- The empty support is always in the structured dual code. -/
theorem isStructuredDualSupport_empty
    (n m : Nat) (hn : 0 < n) :
    IsStructuredDualSupport n (structuredIndependence m) hn ∅ := by
  rw [isStructuredDualSupport_iff]
  intro polynomial
  simp

/-- Exact split of the bilinear form into its same-support diagonal and its
distinct dual aliases. -/
theorem structuredDualRankCrossForm_eq_diagonal_add_distinct
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction =
      structuredDualRankDiagonalCrossForm n m tailBits cutoff hn htail
          leftFunction rightFunction +
        structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
          leftFunction rightFunction := by
  classical
  unfold structuredDualRankCrossForm structuredDualRankDiagonalCrossForm
    structuredDualRankDistinctCrossForm
  let pairTerm := fun left right : Finset (Fin (2 ^ n)) =>
    coefficient leftFunction left * coefficient rightFunction right *
      (1 / (2 : Rat) ^
        supportPrefixConstraintRank n (structuredIndependence m)
          tailBits hn htail (left ∪ right))
  calc
    (∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
        ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
          if IsStructuredDualSupport n (structuredIndependence m) hn
              (left ∆ right) then pairTerm left right else 0) =
      (∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
        ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
          if left = right then pairTerm left right else 0) +
      (∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
        ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
          if left ≠ right ∧
              IsStructuredDualSupport n (structuredIndependence m) hn
                (left ∆ right) then pairTerm left right else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro left _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro right _
          by_cases heq : left = right
          · subst right
            simp [isStructuredDualSupport_empty]
          · by_cases hdual : IsStructuredDualSupport n
                (structuredIndependence m) hn (left ∆ right)
            · simp [heq, hdual]
            · simp [heq, hdual]
    _ = (∑ support ∈ highDegreeSupports (2 ^ n) cutoff,
          pairTerm support support) +
        (∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
          ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
            if left ≠ right ∧
                IsStructuredDualSupport n (structuredIndependence m) hn
                  (left ∆ right) then pairTerm left right else 0) := by
          congr 1
          apply Finset.sum_congr rfl
          intro left hleft
          rw [Finset.sum_eq_single left]
          · simp
          · intro right hright hne
            rw [if_neg (Ne.symm hne)]
          · intro hnot
            exact (hnot hleft).elim
    _ = _ := by
      apply congrArg₂ (fun diagonal distinct => diagonal + distinct)
      · apply Finset.sum_congr rfl
        intro support _
        simp [pairTerm]
      · rfl

/-- On a single function, the distinct bilinear form is exactly the existing
rank-weighted dual-far residual; the explicit `far` test is redundant because
distinct dual supports already exceed the code distance. -/
theorem structuredDualRankDistinctCrossForm_self_eq_rankWeightedDualFar
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail f f =
      DPTWStructuredRankWeightedDualCorrelation.structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f := by
  classical
  unfold structuredDualRankDistinctCrossForm
    DPTWStructuredRankWeightedDualCorrelation.structuredRankWeightedDualFarPairCorrelation
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  by_cases hne : left ≠ right
  · by_cases hdual : IsStructuredDualSupport n
        (structuredIndependence m) hn (left ∆ right)
    · have hfar : structuredIndependence m < (left ∆ right).card := by
        by_contra hnot
        have hcard : (left ∆ right).card <= structuredIndependence m :=
          Nat.le_of_not_gt hnot
        exact (not_isStructuredDualSupport_of_nonempty_card_le
          n m hn (left ∆ right) hcard
            (Finset.symmDiff_nonempty.mpr hne)) hdual
      simp [hne, hdual, hfar]
    · simp [hne, hdual]
  · simp [hne]

/-- Every distinct structured dual alias is automatically farther than the
independence degree. -/
theorem structuredIndependence_lt_symmDiff_card_of_distinct_dual
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n))) (hne : left ≠ right)
    (hdual : IsStructuredDualSupport n (structuredIndependence m) hn
      (left ∆ right)) :
    structuredIndependence m < (left ∆ right).card := by
  by_contra hnot
  have hcard : (left ∆ right).card <= structuredIndependence m :=
    Nat.le_of_not_gt hnot
  exact (not_isStructuredDualSupport_of_nonempty_card_le
    n m hn (left ∆ right) hcard (Finset.symmDiff_nonempty.mpr hne)) hdual

/-- The union support of a distinct dual alias saturates at least all
`structuredIndependence m * tailBits` interpolation constraints. -/
theorem structuredIndependence_mul_tailBits_le_unionRank_of_distinct_dual
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (left right : Finset (Fin (2 ^ n))) (hne : left ≠ right)
    (hdual : IsStructuredDualSupport n (structuredIndependence m) hn
      (left ∆ right)) :
    structuredIndependence m * tailBits <=
      supportPrefixConstraintRank n (structuredIndependence m)
        tailBits hn htail (left ∪ right) := by
  have hfar := structuredIndependence_lt_symmDiff_card_of_distinct_dual
    n m hn left right hne hdual
  have hunionCard : structuredIndependence m <= (left ∪ right).card :=
    (Nat.le_of_lt hfar).trans
      (Finset.card_le_card Finset.symmDiff_subset_union)
  exact supportPrefixConstraintRank_lowerBound
    n (structuredIndependence m) tailBits hn htail
      (left ∪ right) hunionCard

/-- Corresponding unconditional upper bound on every distinct dual-alias
mask weight. -/
theorem distinctDualAlias_invPowUnionRank_le
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (left right : Finset (Fin (2 ^ n))) (hne : left ≠ right)
    (hdual : IsStructuredDualSupport n (structuredIndependence m) hn
      (left ∆ right)) :
    (1 / (2 : Rat) ^
        supportPrefixConstraintRank n (structuredIndependence m)
          tailBits hn htail (left ∪ right)) <=
      1 / (2 : Rat) ^ (structuredIndependence m * tailBits) := by
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_right₀ (by norm_num)
      (structuredIndependence_mul_tailBits_le_unionRank_of_distinct_dual
        n m tailBits hn htail left right hne hdual)

/-- Every support in the strict degree-`2m` tail imposes at least
`(2m+1) * tailBits` independent mask constraints. -/
theorem cutoffSucc_mul_tailBits_le_rank_of_highSupport
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n)))
    (hhigh : support ∈ highDegreeSupports (2 ^ n) (2 * m)) :
    (2 * m + 1) * tailBits <=
      supportPrefixConstraintRank n (structuredIndependence m)
        tailBits hn htail support := by
  have hcardLower : 2 * m + 1 <= support.card := by
    have := mem_highDegreeSupports.mp hhigh
    omega
  by_cases hsmall : support.card <= structuredIndependence m
  · rw [supportPrefixConstraintRank_eq_card_mul
      n (structuredIndependence m) tailBits hn htail support hsmall]
    exact Nat.mul_le_mul_right tailBits hcardLower
  · have hlarge : structuredIndependence m <= support.card :=
      Nat.le_of_not_ge hsmall
    have hrank := supportPrefixConstraintRank_lowerBound
      n (structuredIndependence m) tailBits hn htail support hlarge
    have hcutoff : 2 * m + 1 <= structuredIndependence m := by
      unfold structuredIndependence
      omega
    exact (Nat.mul_le_mul_right tailBits hcutoff).trans hrank

/-- Consequently every same-support diagonal weight in the strict
degree-`2m` tail is at most `2^-((2m+1) * tailBits)`. -/
theorem highSupport_invPowRank_le_cutoffSucc
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n)))
    (hhigh : support ∈ highDegreeSupports (2 ^ n) (2 * m)) :
    (1 / (2 : Rat) ^
        supportPrefixConstraintRank n (structuredIndependence m)
          tailBits hn htail support) <=
      1 / (2 : Rat) ^ ((2 * m + 1) * tailBits) := by
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_right₀ (by norm_num)
      (cutoffSucc_mul_tailBits_le_rank_of_highSupport
        n m tailBits hn htail support hhigh)

/-! ## Canonical sibling cones -/

/-- Two distinct one-step extensions of the same suffix key define disjoint
canonical suffix cones.  The proof uses only uniqueness of an accepted input
and uniqueness of an equal-length suffix of its canonical trace. -/
theorem canonicalDistinctSiblingConeIndicators_mul_eq_zero
    {coordinateCount : Nat}
    (B : FiniteUnambiguousFBDD coordinateCount)
    (key : List B.InputLabelledFullStep)
    (leftStep rightStep : B.InputLabelledFullStep)
    (hne : leftStep ≠ rightStep)
    (input : Fin coordinateCount → Bool) :
    B.canonicalResidualSuffixConeIndicator (leftStep :: key) input *
        B.canonicalResidualSuffixConeIndicator (rightStep :: key) input = 0 := by
  classical
  have hconesDisjoint :
      ¬ (B.IsCanonicalResidualSuffixConeInput (leftStep :: key) input ∧
        B.IsCanonicalResidualSuffixConeInput (rightStep :: key) input) := by
    rintro ⟨⟨leftAccepted, hleftInput, hleftSuffix⟩,
      ⟨rightAccepted, hrightInput, hrightSuffix⟩⟩
    have haccepted : leftAccepted = rightAccepted := by
      apply Subtype.ext
      exact hleftInput.trans hrightInput.symm
    subst rightAccepted
    have hkeys : leftStep :: key = rightStep :: key := by
      rcases List.suffix_or_suffix_of_suffix hleftSuffix hrightSuffix with
        hleftRight | hrightLeft
      · exact hleftRight.eq_of_length (by simp)
      · exact (hrightLeft.eq_of_length (by simp)).symm
    exact hne (List.cons.inj hkeys).1
  rw [B.canonicalResidualSuffixConeIndicator_eq_membershipIndicator,
    B.canonicalResidualSuffixConeIndicator_eq_membershipIndicator]
  unfold canonicalResidualSuffixConeMembershipIndicator
  by_cases hleft :
      B.IsCanonicalResidualSuffixConeInput (leftStep :: key) input
  · have hright :
        ¬ B.IsCanonicalResidualSuffixConeInput (rightStep :: key) input := by
      intro hright
      exact hconesDisjoint ⟨hleft, hright⟩
    simp [hleft, hright]
  · simp [hleft]

/-- Hence the complete, unweighted Fourier convolution of two distinct
sibling cones vanishes at every symmetric-difference support `W`. -/
theorem canonicalDistinctSiblingCone_symmDiffConvolution_eq_zero
    {coordinateCount : Nat}
    (B : FiniteUnambiguousFBDD coordinateCount)
    (key : List B.InputLabelledFullStep)
    (leftStep rightStep : B.InputLabelledFullStep)
    (hne : leftStep ≠ rightStep)
    (W : Finset (Fin coordinateCount)) :
    (∑ alpha : Finset (Fin coordinateCount),
        coefficient
            (B.canonicalResidualSuffixConeIndicator (leftStep :: key)) alpha *
          coefficient
            (B.canonicalResidualSuffixConeIndicator (rightStep :: key))
              (alpha ∆ W)) = 0 := by
  exact disjoint_symmDiff_convolution_eq_zero
    (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
    (B.canonicalResidualSuffixConeIndicator (rightStep :: key))
    (canonicalDistinctSiblingConeIndicators_mul_eq_zero
      B key leftStep rightStep hne) W

/-- Exact selector-specific low/high transfer for distinct sibling cones.
The high/high predicate selects alias pairs whose two endpoint degrees exceed
`cutoff`; no estimate on the low remainder or weight variation is asserted. -/
theorem canonicalDistinctSiblingCone_weightedHighHighTransfer
    {coordinateCount : Nat}
    (B : FiniteUnambiguousFBDD coordinateCount)
    (key : List B.InputLabelledFullStep)
    (leftStep rightStep : B.InputLabelledFullStep)
    (hne : leftStep ≠ rightStep)
    (weight : Finset (Fin coordinateCount) → Rat)
    (cutoff : Nat) (W : Finset (Fin coordinateCount))
    (baseWeight : Rat) :
    weightedSelectedSum (highHighAlias cutoff W) weight
        (fun alpha =>
          coefficient
              (B.canonicalResidualSuffixConeIndicator (leftStep :: key)) alpha *
            coefficient
              (B.canonicalResidualSuffixConeIndicator (rightStep :: key))
                (alpha ∆ W)) =
      -baseWeight *
          rejectedSum (highHighAlias cutoff W)
            (fun alpha =>
              coefficient
                  (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
                    alpha *
                coefficient
                  (B.canonicalResidualSuffixConeIndicator
                    (rightStep :: key)) (alpha ∆ W)) +
        selectedWeightVariation (highHighAlias cutoff W) weight
          (fun alpha =>
            coefficient
                (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
                  alpha *
              coefficient
                (B.canonicalResidualSuffixConeIndicator (rightStep :: key))
                  (alpha ∆ W)) baseWeight := by
  apply weightedSelectedSum_eq_neg_base_mul_rejectedSum_add_variation
  exact canonicalDistinctSiblingCone_symmDiffConvolution_eq_zero
    B key leftStep rightStep hne W

/-- Cross moment of two immediate reverse-trie extensions of one canonical
suffix key, expressed as the exact full dual-rank form. -/
theorem canonicalSiblingConeCrossMoment_eq_dualRankCrossForm
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (key : List (B.InputLabelledFullStep))
    (leftStep rightStep : B.InputLabelledFullStep) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          (leftStep :: key) *
        B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          (rightStep :: key)) =
      structuredDualRankCrossForm n m tailBits (2 * m) hn htail
        (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
        (B.canonicalResidualSuffixConeIndicator (rightStep :: key)) := by
  calc
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          (leftStep :: key) *
        B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          (rightStep :: key)) =
      structuredHighTailCrossMoment n m tailBits (2 * m) hn htail
        (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
        (B.canonicalResidualSuffixConeIndicator (rightStep :: key)) := by
          unfold structuredHighTailCrossMoment
          apply finiteAverage_congr
          intro seed
          rw [B.canonicalResidualDeviationSuffixConeMass_eq_highTailAverage,
            B.canonicalResidualDeviationSuffixConeMass_eq_highTailAverage]
    _ = _ := structuredHighTailCrossMoment_eq_dualRankCrossForm
      n m tailBits (2 * m) hn htail
        (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
        (B.canonicalResidualSuffixConeIndicator (rightStep :: key))

/-- Diagonal-plus-distinct-dual decomposition of one sibling-cone cross
moment. -/
theorem canonicalSiblingConeCrossMoment_eq_diagonal_add_distinct
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (key : List (B.InputLabelledFullStep))
    (leftStep rightStep : B.InputLabelledFullStep) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          (leftStep :: key) *
        B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          (rightStep :: key)) =
      structuredDualRankDiagonalCrossForm n m tailBits (2 * m) hn htail
          (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
          (B.canonicalResidualSuffixConeIndicator (rightStep :: key)) +
        structuredDualRankDistinctCrossForm n m tailBits (2 * m) hn htail
          (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
          (B.canonicalResidualSuffixConeIndicator (rightStep :: key)) := by
  rw [canonicalSiblingConeCrossMoment_eq_dualRankCrossForm]
  exact structuredDualRankCrossForm_eq_diagonal_add_distinct
    n m tailBits (2 * m) hn htail
      (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
      (B.canonicalResidualSuffixConeIndicator (rightStep :: key))

/-- A one-sided sibling frame estimate is therefore literally the displayed
diagonal-plus-distinct coefficient inequality, with no hidden structural
premise. -/
theorem canonicalSiblingConeCrossMoment_le_iff_dualRankCoefficientBudget
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (key : List (B.InputLabelledFullStep))
    (leftStep rightStep : B.InputLabelledFullStep) (budget : Rat) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          (leftStep :: key) *
        B.canonicalResidualDeviationSuffixConeMass (2 * m)
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
          (rightStep :: key)) <= budget ↔
      structuredDualRankDiagonalCrossForm n m tailBits (2 * m) hn htail
          (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
          (B.canonicalResidualSuffixConeIndicator (rightStep :: key)) +
        structuredDualRankDistinctCrossForm n m tailBits (2 * m) hn htail
          (B.canonicalResidualSuffixConeIndicator (leftStep :: key))
          (B.canonicalResidualSuffixConeIndicator (rightStep :: key)) <=
        budget := by
  rw [canonicalSiblingConeCrossMoment_eq_diagonal_add_distinct]

/-! ## Exact prefix/cylinder phase of one dual-rank entry -/

/-- After the complete-cone factorization, one dual-rank matrix entry is an
exact product of two reachable-prefix coefficients, two suffix character
phases, and three dyadic damping factors. -/
theorem realizedConeDualRankEntry_eq_prefixPhase
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hUnambiguous : B.IsUnambiguous)
    (leftReference rightReference : B.AcceptedModel)
    {leftVertex rightVertex : B.Vertex}
    (leftSuffix : B.Walk leftVertex B.accept)
    (rightSuffix : B.Walk rightVertex B.accept)
    (hleftSuffix : B.HasCanonicalAcceptingSuffix leftReference leftSuffix)
    (hrightSuffix : B.HasCanonicalAcceptingSuffix rightReference rightSuffix)
    (hleftComplete :
      (B.canonicalAcceptingWalk leftReference).queryVars = Finset.univ)
    (hrightComplete :
      (B.canonicalAcceptingWalk rightReference).queryVars = Finset.univ)
    (left right : Finset (Fin (2 ^ n))) :
    coefficient
          (B.canonicalResidualSuffixConeIndicator
            (leftSuffix.inputLabelledFullTrace leftReference.1)) left *
        coefficient
          (B.canonicalResidualSuffixConeIndicator
            (rightSuffix.inputLabelledFullTrace rightReference.1)) right *
        (1 / (2 : Rat) ^
          supportPrefixConstraintRank n (structuredIndependence m)
            tailBits hn htail (left ∪ right)) =
      (coefficient (fun input =>
            B.ratCompatiblePrefixIndicator input leftVertex)
            (left ∩ B.preVars leftVertex) *
          coefficient (fun input =>
            B.ratCompatiblePrefixIndicator input rightVertex)
            (right ∩ B.preVars rightVertex) *
          character (left ∩ leftSuffix.queryVars) leftReference.1 *
          character (right ∩ rightSuffix.queryVars) rightReference.1) /
        ((2 : Rat) ^ leftSuffix.queryVars.card *
          (2 : Rat) ^ rightSuffix.queryVars.card *
          (2 : Rat) ^
            supportPrefixConstraintRank n (structuredIndependence m)
              tailBits hn htail (left ∪ right)) := by
  rw [B.coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_character_div_of_complete
      hreadOnce hUnambiguous leftReference leftSuffix hleftSuffix
        hleftComplete left,
    B.coefficient_canonicalResidualSuffixConeIndicator_eq_prefix_mul_character_div_of_complete
      hreadOnce hUnambiguous rightReference rightSuffix hrightSuffix
        hrightComplete right]
  ring

/-- Absolute form of the exact phase identity.  The two character phases
disappear, but no rank relaxation occurs. -/
theorem abs_realizedConeDualRankEntry_eq_prefixAbs
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hUnambiguous : B.IsUnambiguous)
    (leftReference rightReference : B.AcceptedModel)
    {leftVertex rightVertex : B.Vertex}
    (leftSuffix : B.Walk leftVertex B.accept)
    (rightSuffix : B.Walk rightVertex B.accept)
    (hleftSuffix : B.HasCanonicalAcceptingSuffix leftReference leftSuffix)
    (hrightSuffix : B.HasCanonicalAcceptingSuffix rightReference rightSuffix)
    (hleftComplete :
      (B.canonicalAcceptingWalk leftReference).queryVars = Finset.univ)
    (hrightComplete :
      (B.canonicalAcceptingWalk rightReference).queryVars = Finset.univ)
    (left right : Finset (Fin (2 ^ n))) :
    |coefficient
          (B.canonicalResidualSuffixConeIndicator
            (leftSuffix.inputLabelledFullTrace leftReference.1)) left *
        coefficient
          (B.canonicalResidualSuffixConeIndicator
            (rightSuffix.inputLabelledFullTrace rightReference.1)) right *
        (1 / (2 : Rat) ^
          supportPrefixConstraintRank n (structuredIndependence m)
            tailBits hn htail (left ∪ right))| =
      (|coefficient (fun input =>
            B.ratCompatiblePrefixIndicator input leftVertex)
            (left ∩ B.preVars leftVertex)| *
          |coefficient (fun input =>
            B.ratCompatiblePrefixIndicator input rightVertex)
            (right ∩ B.preVars rightVertex)|) /
        ((2 : Rat) ^ leftSuffix.queryVars.card *
          (2 : Rat) ^ rightSuffix.queryVars.card *
          (2 : Rat) ^
            supportPrefixConstraintRank n (structuredIndependence m)
              tailBits hn htail (left ∪ right)) := by
  rw [realizedConeDualRankEntry_eq_prefixPhase
    n m tailBits hn htail B hreadOnce hUnambiguous
      leftReference rightReference leftSuffix rightSuffix hleftSuffix
      hrightSuffix hleftComplete hrightComplete left right]
  rw [abs_div]
  simp only [abs_mul, abs_character_eq_one, mul_one]
  rw [abs_of_nonneg (by positivity :
        (0 : Rat) <= (2 : Rat) ^ leftSuffix.queryVars.card),
    abs_of_nonneg (by positivity :
        (0 : Rat) <= (2 : Rat) ^ rightSuffix.queryVars.card),
    abs_of_nonneg (by positivity :
        (0 : Rat) <= (2 : Rat) ^
          supportPrefixConstraintRank n (structuredIndependence m)
            tailBits hn htail (left ∪ right))]

/-- Strongest unconditional termwise rank/phase estimate available from the
current code geometry: every distinct dual alias pays both suffix-cylinder
normalizations and the full `(4m+1) * tailBits` mask-rank damping. -/
theorem abs_realizedConeDistinctDualRankEntry_le
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (B : FiniteUnambiguousFBDD (2 ^ n))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hUnambiguous : B.IsUnambiguous)
    (leftReference rightReference : B.AcceptedModel)
    {leftVertex rightVertex : B.Vertex}
    (leftSuffix : B.Walk leftVertex B.accept)
    (rightSuffix : B.Walk rightVertex B.accept)
    (hleftSuffix : B.HasCanonicalAcceptingSuffix leftReference leftSuffix)
    (hrightSuffix : B.HasCanonicalAcceptingSuffix rightReference rightSuffix)
    (hleftComplete :
      (B.canonicalAcceptingWalk leftReference).queryVars = Finset.univ)
    (hrightComplete :
      (B.canonicalAcceptingWalk rightReference).queryVars = Finset.univ)
    (left right : Finset (Fin (2 ^ n))) (hne : left ≠ right)
    (hdual : IsStructuredDualSupport n (structuredIndependence m) hn
      (left ∆ right)) :
    |coefficient
          (B.canonicalResidualSuffixConeIndicator
            (leftSuffix.inputLabelledFullTrace leftReference.1)) left *
        coefficient
          (B.canonicalResidualSuffixConeIndicator
            (rightSuffix.inputLabelledFullTrace rightReference.1)) right *
        (1 / (2 : Rat) ^
          supportPrefixConstraintRank n (structuredIndependence m)
            tailBits hn htail (left ∪ right))| <=
      (|coefficient (fun input =>
            B.ratCompatiblePrefixIndicator input leftVertex)
            (left ∩ B.preVars leftVertex)| *
          |coefficient (fun input =>
            B.ratCompatiblePrefixIndicator input rightVertex)
            (right ∩ B.preVars rightVertex)|) /
        ((2 : Rat) ^ leftSuffix.queryVars.card *
          (2 : Rat) ^ rightSuffix.queryVars.card *
          (2 : Rat) ^ (structuredIndependence m * tailBits)) := by
  let prefixAbs : Rat :=
    |coefficient (fun input =>
        B.ratCompatiblePrefixIndicator input leftVertex)
        (left ∩ B.preVars leftVertex)| *
      |coefficient (fun input =>
        B.ratCompatiblePrefixIndicator input rightVertex)
        (right ∩ B.preVars rightVertex)|
  let suffixScale : Rat :=
    (2 : Rat) ^ leftSuffix.queryVars.card *
      (2 : Rat) ^ rightSuffix.queryVars.card
  have hprefixAbs : 0 <= prefixAbs := by
    dsimp only [prefixAbs]
    positivity
  have hsuffixScale : 0 < suffixScale := by
    dsimp only [suffixScale]
    positivity
  have hrankWeight := distinctDualAlias_invPowUnionRank_le
    n m tailBits hn htail left right hne hdual
  rw [abs_realizedConeDualRankEntry_eq_prefixAbs
    n m tailBits hn htail B hreadOnce hUnambiguous
      leftReference rightReference leftSuffix rightSuffix hleftSuffix
      hrightSuffix hleftComplete hrightComplete left right]
  change
    prefixAbs /
        (suffixScale *
          (2 : Rat) ^
            supportPrefixConstraintRank n (structuredIndependence m)
              tailBits hn htail (left ∪ right)) <=
      prefixAbs /
        (suffixScale *
          (2 : Rat) ^ (structuredIndependence m * tailBits))
  calc
    prefixAbs /
        (suffixScale *
          (2 : Rat) ^
            supportPrefixConstraintRank n (structuredIndependence m)
              tailBits hn htail (left ∪ right)) =
      (prefixAbs / suffixScale) *
        (1 / (2 : Rat) ^
          supportPrefixConstraintRank n (structuredIndependence m)
            tailBits hn htail (left ∪ right)) := by ring
    _ <= (prefixAbs / suffixScale) *
        (1 / (2 : Rat) ^ (structuredIndependence m * tailBits)) := by
          exact mul_le_mul_of_nonneg_left hrankWeight
            (div_nonneg hprefixAbs (le_of_lt hsuffixScale))
    _ = prefixAbs /
        (suffixScale *
          (2 : Rat) ^ (structuredIndependence m * tailBits)) := by ring

end FiniteSignedReverseLCPSiblingDualRank

end

end OneTapeMagnification
end Frontier
end Pnp4
