import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPSiblingDualRank
import Pnp4.Frontier.OneTapeMagnification.FiniteRankWeightAbelVariation
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorPairCorrelation
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFullFieldCorrelation
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Rank-threshold bridge for the structured selector-pair form

This file turns the exact inverse-rank dual-alias form into finite rank
buckets and cumulative rank-threshold sums.  Abel summation then shows that
a uniform upper bound on every cumulative signed sum controls the weighted
form with no absolute-value relaxation.

The selector-specific cumulative bound is deliberately packaged as a
`Prop`; it is not proved here.  The final theorems prove only that the
explicit constant `4` is sufficient for the existing `DualFarBound` budget
when `m` and `tailBits` are positive.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanFullIndependenceRestriction
open FiniteBooleanBoundedIndependenceFarTail
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open DPTWStructuredRankWeightedDualCorrelation
open DPTWStructuredFullFieldCorrelation
open MandatoryCanonicalSelectorPairCorrelation
open FiniteRankWeightAbelVariation
open FiniteSignedReverseLCPSiblingDualRank

namespace FiniteStructuredDualRankThresholdBridge

/-! ## Generic finite rank buckets and cumulative sums -/

/-- Signed mass in one exact rank bucket. -/
def finiteRankBucketSum {Index : Type*}
    (indices : Finset Index) (rank : Index -> Nat) (term : Index -> Rat)
    (level : Nat) : Rat :=
  ∑ index in indices, if rank index = level then term index else 0

/-- Signed mass whose rank is at most the given threshold. -/
def finiteRankAtMostSum {Index : Type*}
    (indices : Finset Index) (rank : Index -> Nat) (term : Index -> Rat)
    (level : Nat) : Rat :=
  ∑ index in indices, if rank index <= level then term index else 0

/-- Exact reconstruction of a cumulative threshold sum from rank buckets. -/
theorem finiteRankAtMostSum_eq_sum_buckets {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (rank : Index -> Nat) (term : Index -> Rat)
    (level : Nat) :
    finiteRankAtMostSum indices rank term level =
      ∑ bucket in Finset.range (level + 1),
        finiteRankBucketSum indices rank term bucket := by
  classical
  unfold finiteRankAtMostSum finiteRankBucketSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index hindex
  by_cases hrank : rank index <= level
  · rw [if_pos hrank]
    rw [Finset.sum_eq_single (rank index)]
    · simp
    · intro bucket hbucket hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg hrank]
    symm
    apply Finset.sum_eq_zero
    intro bucket hbucket
    rw [if_neg]
    intro heq
    apply hrank
    rw [heq]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hbucket)

/-- Pointwise form of Abel summation: a dyadic weight at `rank` is the
terminal weight plus every successive drop at a threshold above `rank`. -/
theorem dyadicRankWeight_eq_terminal_add_thresholdDrops
    {baseRank rank upperRank : Nat}
    (hlower : baseRank <= rank) (hupper : rank <= upperRank) :
    dyadicRankWeight rank =
      dyadicRankWeight upperRank +
        ∑ level in Finset.Ico baseRank upperRank,
          if rank <= level then dyadicRankWeight (level + 1) else 0 := by
  classical
  have hfilter :
      (∑ level in Finset.Ico baseRank upperRank,
          if rank <= level then dyadicRankWeight (level + 1) else 0) =
        ∑ level in Finset.Ico rank upperRank,
          dyadicRankWeight (level + 1) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext level
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    · intro level hlevel
      rfl
  rw [hfilter]
  have htelescoping := dyadicRankWeight_sub_eq_neg_sum_Ico hupper
  linarith

/-- Finite Abel summation for decreasing dyadic rank weights.  It is stated
with cumulative `rank <= level` sums, so every coefficient on the right is
nonnegative. -/
theorem finiteDyadicRankWeightedSum_eq_terminal_add_cumulative
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (rank : Index -> Nat) (term : Index -> Rat)
    (baseRank upperRank : Nat)
    (hlower : ∀ index ∈ indices, baseRank <= rank index)
    (hupper : ∀ index ∈ indices, rank index <= upperRank) :
    (∑ index in indices, dyadicRankWeight (rank index) * term index) =
      dyadicRankWeight upperRank *
          finiteRankAtMostSum indices rank term upperRank +
        ∑ level in Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) *
            finiteRankAtMostSum indices rank term level := by
  classical
  have hterminal :
      finiteRankAtMostSum indices rank term upperRank =
        ∑ index in indices, term index := by
    unfold finiteRankAtMostSum
    apply Finset.sum_congr rfl
    intro index hindex
    rw [if_pos (hupper index hindex)]
  rw [hterminal, Finset.mul_sum]
  unfold finiteRankAtMostSum
  calc
    (∑ index in indices, dyadicRankWeight (rank index) * term index) =
        ∑ index in indices,
          (dyadicRankWeight upperRank +
              ∑ level in Finset.Ico baseRank upperRank,
                if rank index <= level then
                  dyadicRankWeight (level + 1)
                else 0) * term index := by
      apply Finset.sum_congr rfl
      intro index hindex
      rw [dyadicRankWeight_eq_terminal_add_thresholdDrops
        (hlower index hindex) (hupper index hindex)]
    _ = (∑ index in indices, dyadicRankWeight upperRank * term index) +
        ∑ index in indices,
          ∑ level in Finset.Ico baseRank upperRank,
            dyadicRankWeight (level + 1) *
              (if rank index <= level then term index else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro index hindex
      rw [add_mul, Finset.sum_mul]
      apply congrArg (fun value =>
        dyadicRankWeight upperRank * term index + value)
      apply Finset.sum_congr rfl
      intro level hlevel
      by_cases hrank : rank index <= level <;> simp [hrank]
    _ = (∑ index in indices, dyadicRankWeight upperRank * term index) +
        ∑ level in Finset.Ico baseRank upperRank,
          ∑ index in indices,
            dyadicRankWeight (level + 1) *
              (if rank index <= level then term index else 0) := by
      rw [Finset.sum_comm]
    _ = (∑ index in indices, dyadicRankWeight upperRank * term index) +
        ∑ level in Finset.Ico baseRank upperRank,
          dyadicRankWeight (level + 1) *
            ∑ index in indices,
              (if rank index <= level then term index else 0) := by
      apply congrArg (fun value =>
        (∑ index in indices, dyadicRankWeight upperRank * term index) + value)
      apply Finset.sum_congr rfl
      intro level hlevel
      rw [Finset.mul_sum]

/-! ## Actual structured dual-alias pairs -/

/-- The finite set of ordered high-degree, distinct structured-dual pairs. -/
def structuredDualAliasPairs
    (n m cutoff : Nat) (hn : 0 < n) :
    Finset (Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n))) := by
  classical
  exact
    ((highDegreeSupports (2 ^ n) cutoff).product
      (highDegreeSupports (2 ^ n) cutoff)).filter (fun pair =>
        pair.1 ≠ pair.2 ∧
          IsStructuredDualSupport n (structuredIndependence m) hn
            (pair.1 ∆ pair.2))

/-- Actual prefix-constraint rank of the union support of one alias pair. -/
def structuredDualAliasPairRank
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (pair : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n))) : Nat :=
  supportPrefixConstraintRank n (structuredIndependence m)
    tailBits hn htail (pair.1 ∪ pair.2)

/-- Product of the two Fourier coefficients attached to an ordered pair. -/
def structuredDualAliasPairCoefficient
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (pair : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n))) : Rat :=
  coefficient leftFunction pair.1 * coefficient rightFunction pair.2

/-- Signed mass in the exact actual-rank bucket. -/
def structuredDualRankBucketCrossForm
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (level : Nat) : Rat :=
  finiteRankBucketSum (structuredDualAliasPairs n m cutoff hn)
    (structuredDualAliasPairRank n m tailBits hn htail)
    (structuredDualAliasPairCoefficient leftFunction rightFunction) level

/-- Cumulative signed dual-alias mass of all pairs with actual union rank at
most `level`. -/
def structuredDualRankAtMostCrossForm
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (level : Nat) : Rat :=
  finiteRankAtMostSum (structuredDualAliasPairs n m cutoff hn)
    (structuredDualAliasPairRank n m tailBits hn htail)
    (structuredDualAliasPairCoefficient leftFunction rightFunction) level

theorem structuredDualRankAtMostCrossForm_eq_sum_buckets
    (n m tailBits cutoff level : Nat) (hn : 0 < n)
    (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction level =
      ∑ bucket in Finset.range (level + 1),
        structuredDualRankBucketCrossForm n m tailBits cutoff hn htail
          leftFunction rightFunction bucket := by
  exact finiteRankAtMostSum_eq_sum_buckets
    (structuredDualAliasPairs n m cutoff hn)
    (structuredDualAliasPairRank n m tailBits hn htail)
    (structuredDualAliasPairCoefficient leftFunction rightFunction) level

theorem mem_structuredDualAliasPairs_iff
    (n m cutoff : Nat) (hn : 0 < n)
    (pair : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n))) :
    pair ∈ structuredDualAliasPairs n m cutoff hn ↔
      pair.1 ∈ highDegreeSupports (2 ^ n) cutoff ∧
      pair.2 ∈ highDegreeSupports (2 ^ n) cutoff ∧
      pair.1 ≠ pair.2 ∧
      IsStructuredDualSupport n (structuredIndependence m) hn
        (pair.1 ∆ pair.2) := by
  classical
  simp [structuredDualAliasPairs, and_assoc]

theorem structuredDualAliasPairRank_lower
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (pair : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)))
    (hpair : pair ∈ structuredDualAliasPairs n m cutoff hn) :
    structuredIndependence m * tailBits <=
      structuredDualAliasPairRank n m tailBits hn htail pair := by
  rw [mem_structuredDualAliasPairs_iff] at hpair
  exact structuredIndependence_mul_tailBits_le_unionRank_of_distinct_dual
    n m tailBits hn htail pair.1 pair.2 hpair.2.2.1 hpair.2.2.2

theorem structuredDualAliasPairRank_upper
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (pair : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n))) :
    structuredDualAliasPairRank n m tailBits hn htail pair <=
      structuredIndependence m * n := by
  exact supportPrefixConstraintRank_upperBound
    n (structuredIndependence m) tailBits hn htail (pair.1 ∪ pair.2)

theorem structuredDualRankDistinctCrossForm_eq_pairWeightedSum
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction =
      ∑ pair in structuredDualAliasPairs n m cutoff hn,
        dyadicRankWeight
            (structuredDualAliasPairRank n m tailBits hn htail pair) *
          structuredDualAliasPairCoefficient leftFunction rightFunction pair := by
  classical
  unfold structuredDualRankDistinctCrossForm structuredDualAliasPairs
    structuredDualAliasPairRank structuredDualAliasPairCoefficient
    dyadicRankWeight
  rw [Finset.sum_filter]
  let high := highDegreeSupports (2 ^ n) cutoff
  let pairTerm := fun pair :
      Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) =>
    if pair.1 ≠ pair.2 ∧
        IsStructuredDualSupport n (structuredIndependence m) hn
          (pair.1 ∆ pair.2) then
      coefficient leftFunction pair.1 * coefficient rightFunction pair.2 *
        (1 / (2 : Rat) ^
          supportPrefixConstraintRank n (structuredIndependence m)
            tailBits hn htail (pair.1 ∪ pair.2))
    else 0
  change
    (∑ left in high, ∑ right in high, pairTerm (left, right)) =
      ∑ pair in high.product high,
        if pair.1 ≠ pair.2 ∧
            IsStructuredDualSupport n (structuredIndependence m) hn
              (pair.1 ∆ pair.2) then
          (1 / (2 : Rat) ^
              supportPrefixConstraintRank n (structuredIndependence m)
                tailBits hn htail (pair.1 ∪ pair.2)) *
            (coefficient leftFunction pair.1 * coefficient rightFunction pair.2)
        else 0
  calc
    (∑ left in high, ∑ right in high, pairTerm (left, right)) =
        ∑ pair in high.product high, pairTerm pair := by
      exact (Finset.sum_product high high pairTerm).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pair hpairMem
      by_cases hpair : pair.1 ≠ pair.2 ∧
          IsStructuredDualSupport n (structuredIndependence m) hn
            (pair.1 ∆ pair.2)
      · simp [pairTerm, hpair]
        ring
      · simp [pairTerm, hpair]

/-- Exact Abel decomposition of the actual structured distinct-alias form
into cumulative actual-rank partial sums. -/
theorem structuredDualRankDistinctCrossForm_eq_terminal_add_cumulative
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction =
      dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
            leftFunction rightFunction (structuredIndependence m * n) +
        ∑ level in Finset.Ico
            (structuredIndependence m * tailBits)
            (structuredIndependence m * n),
          dyadicRankWeight (level + 1) *
            structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
              leftFunction rightFunction level := by
  rw [structuredDualRankDistinctCrossForm_eq_pairWeightedSum]
  exact finiteDyadicRankWeightedSum_eq_terminal_add_cumulative
    (structuredDualAliasPairs n m cutoff hn)
    (structuredDualAliasPairRank n m tailBits hn htail)
    (structuredDualAliasPairCoefficient leftFunction rightFunction)
    (structuredIndependence m * tailBits)
    (structuredIndependence m * n)
    (structuredDualAliasPairRank_lower n m tailBits cutoff hn htail)
    (fun pair _ => structuredDualAliasPairRank_upper
      n m tailBits hn htail pair)

/-- Self-specialization of the Abel identity, stated directly for the exact
rank-weighted dual-far residual used downstream. -/
theorem structuredRankWeightedDualFarPairCorrelation_eq_terminal_add_cumulative
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits cutoff hn htail f =
      dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
            f f (structuredIndependence m * n) +
        ∑ level in Finset.Ico
            (structuredIndependence m * tailBits)
            (structuredIndependence m * n),
          dyadicRankWeight (level + 1) *
            structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
              f f level := by
  rw [← structuredDualRankDistinctCrossForm_self_eq_rankWeightedDualFar]
  exact structuredDualRankDistinctCrossForm_eq_terminal_add_cumulative
    n m tailBits cutoff hn htail f f

/-! ## The terminal threshold is unconditional -/

/-- At the terminal rank threshold every actual dual-alias pair is present,
so the cumulative sum is exactly the unweighted pair-coefficient sum. -/
theorem structuredDualRankAtMostCrossForm_terminal_eq_pairCoefficientSum
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat) :
    structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction (structuredIndependence m * n) =
      ∑ pair in structuredDualAliasPairs n m cutoff hn,
        structuredDualAliasPairCoefficient leftFunction rightFunction pair := by
  unfold structuredDualRankAtMostCrossForm finiteRankAtMostSum
  apply Finset.sum_congr rfl
  intro pair hpair
  rw [if_pos (structuredDualAliasPairRank_upper
    n m tailBits hn htail pair)]

/-- The terminal self-pair sum is exactly the structured base-source far
correlation with the all-false mask.  The explicit `far` predicate is
redundant on a distinct nonempty structured-dual word. -/
theorem structuredDualAliasPairCoefficientSum_self_eq_allFalseFar
    (n m cutoff : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) :
    (∑ pair in structuredDualAliasPairs n m cutoff hn,
        structuredDualAliasPairCoefficient f f pair) =
      highTailFarPairCorrelation f cutoff (structuredIndependence m)
        (structuredUnbiasedPrimitive n m hn).generate allFalseMask := by
  classical
  unfold structuredDualAliasPairs structuredDualAliasPairCoefficient
    highTailFarPairCorrelation
  rw [Finset.sum_filter]
  refine (Finset.sum_product
    (highDegreeSupports (2 ^ n) cutoff)
    (highDegreeSupports (2 ^ n) cutoff)
    (fun pair =>
      if pair.1 ≠ pair.2 ∧
          IsStructuredDualSupport n (structuredIndependence m) hn
            (pair.1 ∆ pair.2) then
        coefficient f pair.1 * coefficient f pair.2
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
      rw [structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq]
      simp [hdual, allFalseMask, maskAllZeroIndicator, finiteAverage]
    · rw [if_neg (by simp [hdual])]
      by_cases hfar : structuredIndependence m < (left ∆ right).card
      · rw [if_pos ⟨hne, hfar⟩]
        rw [structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq]
        simp [hdual]
      · rw [if_neg (by simp [hfar])]
  · simp [hne]

/-- Consequently the terminal cumulative threshold is unconditionally at
most `4` for every pointwise-`1`-bounded function. -/
theorem structuredDualRankAtMostCrossForm_terminal_le_four
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : ∀ input, |f input| <= 1) :
    structuredDualRankAtMostCrossForm n m tailBits (2 * m) hn htail
        f f (structuredIndependence m * n) <= 4 := by
  rw [structuredDualRankAtMostCrossForm_terminal_eq_pairCoefficientSum]
  rw [structuredDualAliasPairCoefficientSum_self_eq_allFalseFar]
  exact (le_abs_self _).trans
    (abs_structured_allFalse_highTailFarPairCorrelation_le_four
      n m hn f hbounded)

/-! ## Honest cumulative criterion and the `DualFarBound` budget -/

/-- The still-open signed partial-sum statement.  It says that every
cumulative actual-rank threshold of the distinct dual-alias form is at most
`cap`; it does not take absolute values. -/
def StructuredDualRankCumulativeBound
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (cap : Rat) : Prop :=
  ∀ level,
    structuredIndependence m * tailBits <= level ->
    level <= structuredIndependence m * n ->
    structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
      leftFunction rightFunction level <= cap

/-- The genuinely open part of the cumulative criterion: only thresholds
strictly below the terminal seed-space rank are requested. -/
def StructuredDualRankStrictIntermediateCumulativeBound
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (cap : Rat) : Prop :=
  ∀ level,
    structuredIndependence m * tailBits <= level ->
    level < structuredIndependence m * n ->
    structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
      leftFunction rightFunction level <= cap

/-- A strict-intermediate criterion plus a terminal estimate gives the full
cumulative criterion.  This generic lemma makes the endpoint bookkeeping
explicit. -/
theorem structuredDualRankCumulativeBound_of_strictIntermediate_of_terminal
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (cap : Rat)
    (hstrict : StructuredDualRankStrictIntermediateCumulativeBound
      n m tailBits cutoff hn htail leftFunction rightFunction cap)
    (hterminal :
      structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction (structuredIndependence m * n) <= cap) :
    StructuredDualRankCumulativeBound n m tailBits cutoff hn htail
      leftFunction rightFunction cap := by
  intro level hbase hupper
  rcases hupper.lt_or_eq with hlt | heq
  · exact hstrict level hbase hlt
  · subst level
    exact hterminal

/-- For a bounded self-pair at cutoff `2m`, the full cumulative-four
criterion is equivalent to its strict-intermediate part: the terminal
threshold is supplied unconditionally by the preceding theorem. -/
theorem structuredDualRankCumulativeBound_four_iff_strictIntermediate_of_bounded
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hbounded : ∀ input, |f input| <= 1) :
    StructuredDualRankCumulativeBound
        n m tailBits (2 * m) hn htail f f 4 ↔
      StructuredDualRankStrictIntermediateCumulativeBound
        n m tailBits (2 * m) hn htail f f 4 := by
  constructor
  · intro hfull level hbase hupper
    exact hfull level hbase (Nat.le_of_lt hupper)
  · intro hstrict
    exact structuredDualRankCumulativeBound_of_strictIntermediate_of_terminal
      n m tailBits (2 * m) hn htail f f 4 hstrict
        (structuredDualRankAtMostCrossForm_terminal_le_four
          n m tailBits hn htail f hbounded)

/-- A uniform cumulative cap bounds the exact weighted distinct-alias form
by the cap times the largest dyadic weight permitted by the rank floor. -/
theorem structuredDualRankDistinctCrossForm_le_cap_mul_baseWeight
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (leftFunction rightFunction : (Fin (2 ^ n) -> Bool) -> Rat)
    (cap : Rat)
    (hcumulative : StructuredDualRankCumulativeBound
      n m tailBits cutoff hn htail leftFunction rightFunction cap) :
    structuredDualRankDistinctCrossForm n m tailBits cutoff hn htail
        leftFunction rightFunction <=
      cap * dyadicRankWeight (structuredIndependence m * tailBits) := by
  rw [structuredDualRankDistinctCrossForm_eq_terminal_add_cumulative]
  have hbaseUpper : structuredIndependence m * tailBits <=
      structuredIndependence m * n :=
    Nat.mul_le_mul_left (structuredIndependence m) htail
  have hterminal := hcumulative (structuredIndependence m * n)
    hbaseUpper (Nat.le_refl _)
  have hsum :
      (∑ level in Finset.Ico
          (structuredIndependence m * tailBits)
          (structuredIndependence m * n),
        dyadicRankWeight (level + 1) *
          structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
            leftFunction rightFunction level) <=
      ∑ level in Finset.Ico
          (structuredIndependence m * tailBits)
          (structuredIndependence m * n),
        dyadicRankWeight (level + 1) * cap := by
    apply Finset.sum_le_sum
    intro level hlevel
    exact mul_le_mul_of_nonneg_left
      (hcumulative level (by simpa using (Finset.mem_Ico.mp hlevel).1)
        (Nat.le_of_lt (Finset.mem_Ico.mp hlevel).2))
      (dyadicRankWeight_nonneg (level + 1))
  calc
    dyadicRankWeight (structuredIndependence m * n) *
          structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
            leftFunction rightFunction (structuredIndependence m * n) +
        ∑ level in Finset.Ico
            (structuredIndependence m * tailBits)
            (structuredIndependence m * n),
          dyadicRankWeight (level + 1) *
            structuredDualRankAtMostCrossForm n m tailBits cutoff hn htail
              leftFunction rightFunction level <=
      dyadicRankWeight (structuredIndependence m * n) * cap +
        ∑ level in Finset.Ico
            (structuredIndependence m * tailBits)
            (structuredIndependence m * n),
          dyadicRankWeight (level + 1) * cap := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hterminal
          (dyadicRankWeight_nonneg _)) hsum
    _ = cap * dyadicRankWeight (structuredIndependence m * tailBits) := by
      rw [← Finset.sum_mul]
      rw [sum_dyadicRankWeight_succ_Ico hbaseUpper]
      ring

/-- The constant `4` at the minimum distinct-alias rank fits the exact
off-diagonal budget for every positive `m` and positive `tailBits`. -/
theorem four_mul_dyadicStructuredBaseWeight_le_dualFarBudget
    (m tailBits : Nat) (hm : 0 < m) (htail : 0 < tailBits) :
    4 * dyadicRankWeight (structuredIndependence m * tailBits) <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
        (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  let p : Rat := 1 / (2 : Rat) ^ tailBits
  have hp0 : 0 <= p := by
    dsimp [p]
    positivity
  have hpHalf : p <= (1 / 2 : Rat) := by
    dsimp [p]
    apply one_div_le_one_div_of_le (by norm_num : (0 : Rat) < 2)
    exact_mod_cast (show 2 <= 2 ^ tailBits by
      calc
        2 = 2 ^ (1 : Nat) := by norm_num
        _ <= 2 ^ tailBits := Nat.pow_le_pow_right (by norm_num) htail)
  have hp1 : p <= 1 := hpHalf.trans (by norm_num)
  have htailCube : p ^ (2 * m + 1) <= (1 / 8 : Rat) := by
    calc
      p ^ (2 * m + 1) <= p ^ 3 :=
        pow_le_pow_of_le_one hp0 hp1 (by omega)
      _ <= (1 / 2 : Rat) ^ 3 := pow_le_pow_left₀ hp0 hpHalf 3
      _ = (1 / 8 : Rat) := by norm_num
  have htailBudget : 4 * p ^ (2 * m + 1) <= 1 - p := by
    nlinarith
  have hweight :
      dyadicRankWeight (structuredIndependence m * tailBits) =
        p ^ structuredIndependence m := by
    dsimp [dyadicRankWeight, p]
    rw [Nat.mul_comm, pow_mul]
    simp [one_div]
  rw [hweight]
  change 4 * p ^ structuredIndependence m <=
    (1 - p) * p ^ (2 * m)
  calc
    4 * p ^ structuredIndependence m =
        p ^ (2 * m) * (4 * p ^ (2 * m + 1)) := by
      unfold structuredIndependence
      rw [show 4 * m + 1 = 2 * m + (2 * m + 1) by omega, pow_add]
      ring
    _ <= p ^ (2 * m) * (1 - p) :=
      mul_le_mul_of_nonneg_left htailBudget (pow_nonneg hp0 _)
    _ = (1 - p) * p ^ (2 * m) := by ring

/-- The explicit cumulative constant `4` implies the existing signed
rank-weighted dual-far budget. -/
theorem structuredRankWeightedDualFarPairCorrelation_le_dualFarBudget_of_cumulativeFour
    (n m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hcumulative : StructuredDualRankCumulativeBound
      n m tailBits (2 * m) hn htail f f 4) :
    structuredRankWeightedDualFarPairCorrelation
        n m tailBits (2 * m) hn htail f <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
        (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  rw [← structuredDualRankDistinctCrossForm_self_eq_rankWeightedDualFar]
  exact (structuredDualRankDistinctCrossForm_le_cap_mul_baseWeight
    n m tailBits (2 * m) hn htail f f 4 hcumulative).trans
      (four_mul_dyadicStructuredBaseWeight_le_dualFarBudget
        m tailBits hm htailPos)

/-- The same cumulative criterion controls the original structured
dual-far correlation appearing in `DualFarBound`. -/
theorem structuredDualFarPairCorrelation_le_dualFarBudget_of_cumulativeFour
    (n m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat)
    (hcumulative : StructuredDualRankCumulativeBound
      n m tailBits (2 * m) hn htail f f 4) :
    structuredDualFarPairCorrelation n m tailBits (2 * m) hn htail f <=
      (1 - 1 / (2 : Rat) ^ tailBits) *
        (1 / (2 : Rat) ^ tailBits) ^ (2 * m) := by
  rw [structuredDualFarPairCorrelation_eq_rankWeighted]
  exact structuredRankWeightedDualFarPairCorrelation_le_dualFarBudget_of_cumulativeFour
    n m tailBits hn hm htailPos htail f hcumulative

/-- Actual mandatory-selector capstone: the still-open cumulative-four
criterion, required after the fixed affine prefix, implies `DualFarBound`. -/
theorem dualFarBound_of_structuredDualRankCumulativeFour
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (hm : 0 < m)
    (htailPos : 0 < tailBits) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n)))
    (hcumulative : StructuredDualRankCumulativeBound
      n m tailBits (2 * m) hn htail
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
        (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
        4) :
    DualFarBound machine n T b m tailBits hn htail rounds := by
  unfold DualFarBound
  exact structuredDualFarPairCorrelation_le_dualFarBudget_of_cumulativeFour
    n m tailBits hn hm htailPos htail
      (prefixedMandatoryCanonicalSelector machine n T b rounds).ratAcceptanceIndicator
      hcumulative

end FiniteStructuredDualRankThresholdBridge
end

end OneTapeMagnification
end Frontier
end Pnp4
