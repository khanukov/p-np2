import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite bounded-independence laws for Boolean sources

This module gives the exact finite pattern laws behind the two distributional
hypotheses in `FiniteBooleanRestrictionMoment`.  A seed is always uniform on
an arbitrary finite nonempty type, so all probabilities are rational finite
averages.

`IsKWisePatternUnbiased q D` says that every assignment on every set of at
most `q` coordinates has probability exactly `2^(-|S|)`.  The biased version
uses false-bit mass `p`, matching the convention in which a false mask bit is
frozen.  These are full cylinder-event laws, rather than aliases for the
character and all-zero moments consumed by the restriction theorem.
-/

namespace FiniteBooleanBoundedIndependence

open scoped BigOperators symmDiff
open FiniteBooleanFourier FiniteBooleanRestrictionMoment

/-! ## Exact finite pattern laws -/

/-- The rational indicator that an ambient Boolean string has a prescribed
assignment on `support`. -/
def localPatternIndicator {n : Nat} (support : Finset (Fin n))
    (pattern : LocalAssignment support) (input : Fin n → Bool) : ℚ :=
  if restrictAssignment support input = pattern then 1 else 0

/-- Product Bernoulli mass of a local pattern when a false bit has mass `p`
and a true bit has mass `1 - p`. -/
def localPatternProductMass {n : Nat} {support : Finset (Fin n)}
    (p : ℚ) (pattern : LocalAssignment support) : ℚ :=
  ∏ queryIndex : ↑support,
    if pattern queryIndex then 1 - p else p

/-- Standard finite `q`-wise unbiasedness: every pattern on at most `q`
coordinates has the uniform cylinder probability. -/
def IsKWisePatternUnbiased {n : Nat} {Seed : Type*}
    [Fintype Seed] [Nonempty Seed]
    (q : Nat) (source : Seed → Fin n → Bool) : Prop :=
  ∀ support : Finset (Fin n), support.card ≤ q →
    ∀ pattern : LocalAssignment support,
      finiteAverage (fun seed : Seed =>
        localPatternIndicator support pattern (source seed)) =
        1 / (2 : ℚ) ^ support.card

/-- Standard finite `q`-wise product law with false-bit mass `p`. -/
def IsKWisePatternFalseBiased {n : Nat} {Seed : Type*}
    [Fintype Seed] [Nonempty Seed]
    (q : Nat) (p : ℚ) (source : Seed → Fin n → Bool) : Prop :=
  ∀ support : Finset (Fin n), support.card ≤ q →
    ∀ pattern : LocalAssignment support,
      finiteAverage (fun seed : Seed =>
        localPatternIndicator support pattern (source seed)) =
        localPatternProductMass p pattern

/-! ## Partitioning an expectation into cylinder events -/

/-- Exactly one local pattern matches a fixed input. -/
theorem sum_localPatternIndicator_mul {n : Nat}
    (support : Finset (Fin n)) (input : Fin n → Bool)
    (observable : LocalAssignment support → ℚ) :
    (∑ pattern : LocalAssignment support,
      observable pattern * localPatternIndicator support pattern input) =
      observable (restrictAssignment support input) := by
  classical
  let actual := restrictAssignment support input
  calc
    (∑ pattern : LocalAssignment support,
        observable pattern * localPatternIndicator support pattern input) =
      observable actual * localPatternIndicator support actual input := by
        apply Fintype.sum_eq_single actual
        intro pattern hpattern
        have hne : actual ≠ pattern := Ne.symm hpattern
        simp [localPatternIndicator, actual, hne]
    _ = observable (restrictAssignment support input) := by
      simp [localPatternIndicator, actual]

/-- The average of a local observable is the sum of its values weighted by
the exact cylinder probabilities of the source. -/
theorem finiteAverage_restrict_eq_sum_pattern {n : Nat}
    {Seed : Type*} [Fintype Seed]
    (source : Seed → Fin n → Bool) (support : Finset (Fin n))
    (observable : LocalAssignment support → ℚ) :
    finiteAverage (fun seed : Seed =>
      observable (restrictAssignment support (source seed))) =
      ∑ pattern : LocalAssignment support,
        observable pattern *
          finiteAverage (fun seed : Seed =>
            localPatternIndicator support pattern (source seed)) := by
  calc
    finiteAverage (fun seed : Seed =>
        observable (restrictAssignment support (source seed))) =
      finiteAverage (fun seed : Seed =>
        ∑ pattern : LocalAssignment support,
          observable pattern *
            localPatternIndicator support pattern (source seed)) := by
      apply finiteAverage_congr
      intro seed
      exact (sum_localPatternIndicator_mul support (source seed) observable).symm
    _ = ∑ pattern : LocalAssignment support,
        finiteAverage (fun seed : Seed =>
          observable pattern *
            localPatternIndicator support pattern (source seed)) := by
      simpa using
        (finiteAverage_finset_sum
          (Seed := Seed) (Index := LocalAssignment support)
          (Finset.univ : Finset (LocalAssignment support))
          (fun pattern seed => observable pattern *
            localPatternIndicator support pattern (source seed)))
    _ = ∑ pattern : LocalAssignment support,
        observable pattern *
          finiteAverage (fun seed : Seed =>
            localPatternIndicator support pattern (source seed)) := by
      apply Finset.sum_congr rfl
      intro pattern _
      exact finiteAverage_const_mul _ _

/-! ## Unbiased patterns imply Walsh cancellation -/

/-- An ambient character on its whole support is the full local character of
the restricted assignment. -/
theorem character_eq_localCharacter_univ {n : Nat}
    (support : Finset (Fin n)) (input : Fin n → Bool) :
    character support input =
      localCharacter (Finset.univ : Finset ↑support)
        (restrictAssignment support input) := by
  have hlift :
      liftLocalSupport support (Finset.univ : Finset ↑support) = support := by
    ext queryIndex
    simp [liftLocalSupport, supportEmbedding]
  calc
    character support input =
        character (liftLocalSupport support
          (Finset.univ : Finset ↑support)) input := by
      rw [hlift]
    _ = localCharacter (Finset.univ : Finset ↑support)
          (restrictAssignment support input) :=
      character_liftLocalSupport (Finset.univ : Finset ↑support) input

/-- The full nonempty local Walsh character sums to zero over its cube. -/
theorem sum_localCharacter_univ_eq_zero {n : Nat}
    {support : Finset (Fin n)} (hsupport : support.Nonempty) :
    (∑ pattern : LocalAssignment support,
      localCharacter (Finset.univ : Finset ↑support) pattern) = 0 := by
  classical
  simp only [localCharacter]
  rw [← Fintype.prod_sum]
  obtain ⟨queryIndex, hqueryIndex⟩ := hsupport
  let localIndex : ↑support := ⟨queryIndex, hqueryIndex⟩
  apply Finset.prod_eq_zero (Finset.mem_univ localIndex)
  norm_num [boolSign]

/-- A standard finite pattern-unbiased source has zero expectation against
every nonempty Walsh character of degree at most `q`. -/
theorem character_average_eq_zero_of_patternUnbiased
    {n q : Nat} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (source : Seed → Fin n → Bool)
    (hsource : IsKWisePatternUnbiased q source)
    (support : Finset (Fin n)) (hcard : support.card ≤ q)
    (hsupport : support.Nonempty) :
    finiteAverage (fun seed : Seed => character support (source seed)) = 0 := by
  calc
    finiteAverage (fun seed : Seed => character support (source seed)) =
      finiteAverage (fun seed : Seed =>
        localCharacter (Finset.univ : Finset ↑support)
          (restrictAssignment support (source seed))) := by
      apply finiteAverage_congr
      intro seed
      exact character_eq_localCharacter_univ support (source seed)
    _ = ∑ pattern : LocalAssignment support,
        localCharacter (Finset.univ : Finset ↑support) pattern *
          finiteAverage (fun seed : Seed =>
            localPatternIndicator support pattern (source seed)) :=
      finiteAverage_restrict_eq_sum_pattern source support
        (localCharacter (Finset.univ : Finset ↑support))
    _ = ∑ pattern : LocalAssignment support,
        localCharacter (Finset.univ : Finset ↑support) pattern *
          (1 / (2 : ℚ) ^ support.card) := by
      apply Finset.sum_congr rfl
      intro pattern _
      rw [hsource support hcard pattern]
    _ = (∑ pattern : LocalAssignment support,
          localCharacter (Finset.univ : Finset ↑support) pattern) *
        (1 / (2 : ℚ) ^ support.card) := by
      rw [Finset.sum_mul]
    _ = 0 := by
      rw [sum_localCharacter_univ_eq_zero hsupport, zero_mul]

/-! ## Orthogonality from `2k`-wise unbiasedness -/

/-- Multiplying Boolean Walsh characters takes symmetric difference of their
supports. -/
theorem character_mul_character_eq_symmDiff {n : Nat}
    (alpha beta : Finset (Fin n)) (input : Fin n → Bool) :
    character alpha input * character beta input =
      character (alpha ∆ beta) input := by
  classical
  let leftOnly := alpha \ beta
  let rightOnly := beta \ alpha
  let common := alpha ∩ beta
  have hleftCommon : Disjoint leftOnly common := by
    rw [Finset.disjoint_left]
    intro queryIndex hleft hcommon
    exact (Finset.mem_sdiff.mp hleft).2 (Finset.mem_inter.mp hcommon).2
  have hrightCommon : Disjoint rightOnly common := by
    rw [Finset.disjoint_left]
    intro queryIndex hright hcommon
    exact (Finset.mem_sdiff.mp hright).2 (Finset.mem_inter.mp hcommon).1
  have hleftRight : Disjoint leftOnly rightOnly := by
    rw [Finset.disjoint_left]
    intro queryIndex hleft hright
    exact (Finset.mem_sdiff.mp hleft).2 (Finset.mem_sdiff.mp hright).1
  have halpha : leftOnly ∪ common = alpha := by
    ext queryIndex
    simp only [leftOnly, common, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter]
    tauto
  have hbeta : rightOnly ∪ common = beta := by
    ext queryIndex
    simp only [rightOnly, common, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter]
    tauto
  have hsymm : leftOnly ∪ rightOnly = alpha ∆ beta := by
    ext queryIndex
    simp only [leftOnly, rightOnly, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_symmDiff]
  calc
    character alpha input * character beta input =
        (character leftOnly input * character common input) *
          (character rightOnly input * character common input) := by
      rw [← halpha, ← hbeta,
        character_union_of_disjoint hleftCommon,
        character_union_of_disjoint hrightCommon]
    _ = (character leftOnly input * character rightOnly input) *
        (character common input * character common input) := by ring
    _ = character leftOnly input * character rightOnly input := by
      rw [character_square, mul_one]
    _ = character (leftOnly ∪ rightOnly) input :=
      (character_union_of_disjoint hleftRight input).symm
    _ = character (alpha ∆ beta) input := by rw [hsymm]

/-- The symmetric difference has size at most the sum of the two support
sizes. -/
theorem card_symmDiff_le_add {n : Nat}
    (alpha beta : Finset (Fin n)) :
    (alpha ∆ beta).card ≤ alpha.card + beta.card := by
  calc
    (alpha ∆ beta).card ≤ (alpha ∪ beta).card :=
      Finset.card_le_card Finset.symmDiff_subset_union
    _ ≤ alpha.card + beta.card := Finset.card_union_le alpha beta

/-- The exact `D`-orthogonality hypothesis required by the restriction moment
theorem follows from the standard finite `2k`-wise unbiased pattern law. -/
theorem hDOrthogonal_of_twoKWisePatternUnbiased
    {n k : Nat} {DSeed : Type*}
    [Fintype DSeed] [Nonempty DSeed]
    (D : DSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased (2 * k) D) :
    ∀ alpha ∈ degreeSupports n k, ∀ beta ∈ degreeSupports n k,
      alpha ≠ beta →
        finiteAverage (fun d : DSeed =>
          character alpha (D d) * character beta (D d)) = 0 := by
  intro alpha halpha beta hbeta hne
  have halphaCard : alpha.card = k := mem_degreeSupports.mp halpha
  have hbetaCard : beta.card = k := mem_degreeSupports.mp hbeta
  have hcard : (alpha ∆ beta).card ≤ 2 * k := by
    calc
      (alpha ∆ beta).card ≤ alpha.card + beta.card :=
        card_symmDiff_le_add alpha beta
      _ = k + k := by rw [halphaCard, hbetaCard]
      _ = 2 * k := by omega
  have hnonempty : (alpha ∆ beta).Nonempty :=
    Finset.symmDiff_nonempty.mpr hne
  calc
    finiteAverage (fun d : DSeed =>
        character alpha (D d) * character beta (D d)) =
      finiteAverage (fun d : DSeed => character (alpha ∆ beta) (D d)) := by
        apply finiteAverage_congr
        intro d
        exact character_mul_character_eq_symmDiff alpha beta (D d)
    _ = 0 :=
      character_average_eq_zero_of_patternUnbiased
        D hD (alpha ∆ beta) hcard hnonempty

/-! ## Biased patterns imply exact all-frozen survival -/

/-- The all-false assignment on a local support. -/
def allFalseAssignment {n : Nat} (support : Finset (Fin n)) :
    LocalAssignment support :=
  fun _queryIndex => false

/-- Matching the all-false local pattern is exactly the mask all-zero
indicator used by the restriction moment theorem. -/
theorem localPatternIndicator_allFalse_eq_maskAllZeroIndicator
    {n : Nat} (support : Finset (Fin n)) (input : Fin n → Bool) :
    localPatternIndicator support (allFalseAssignment support) input =
      maskAllZeroIndicator support input := by
  by_cases hpattern :
      restrictAssignment support input = allFalseAssignment support
  · have hall : ∀ queryIndex ∈ support, input queryIndex = false := by
      intro queryIndex hqueryIndex
      have hvalue := congrFun hpattern ⟨queryIndex, hqueryIndex⟩
      simpa [restrictAssignment, allFalseAssignment] using hvalue
    unfold localPatternIndicator maskAllZeroIndicator
    rw [if_pos hpattern, if_pos hall]
  · have hnotAll : ¬ ∀ queryIndex ∈ support, input queryIndex = false := by
      intro hall
      apply hpattern
      funext queryIndex
      exact hall queryIndex queryIndex.property
    unfold localPatternIndicator maskAllZeroIndicator
    rw [if_neg hpattern, if_neg hnotAll]

/-- The product mass of the all-false pattern is `p^|support|`. -/
@[simp]
theorem localPatternProductMass_allFalse {n : Nat}
    (support : Finset (Fin n)) (p : ℚ) :
    localPatternProductMass p (allFalseAssignment support) =
      p ^ support.card := by
  simp [localPatternProductMass, allFalseAssignment]

/-- The exact `T` mask-survival hypothesis required by the restriction moment
theorem follows from the standard finite `k`-wise biased product law. -/
theorem hTMask_of_kWisePatternFalseBiased
    {n k : Nat} {TSeed : Type*}
    [Fintype TSeed] [Nonempty TSeed]
    (T : TSeed → Fin n → Bool) (p : ℚ)
    (hT : IsKWisePatternFalseBiased k p T) :
    ∀ alpha ∈ degreeSupports n k,
      finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator alpha (T t)) = p ^ k := by
  intro alpha halpha
  have hcard : alpha.card = k := mem_degreeSupports.mp halpha
  calc
    finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator alpha (T t)) =
      finiteAverage (fun t : TSeed =>
        localPatternIndicator alpha (allFalseAssignment alpha) (T t)) := by
          apply finiteAverage_congr
          intro t
          exact
            (localPatternIndicator_allFalse_eq_maskAllZeroIndicator
              alpha (T t)).symm
    _ = localPatternProductMass p (allFalseAssignment alpha) :=
      hT alpha (by omega) (allFalseAssignment alpha)
    _ = p ^ alpha.card := localPatternProductMass_allFalse alpha p
    _ = p ^ k := by rw [hcard]

end FiniteBooleanBoundedIndependence
end OneTapeMagnification
end Frontier
end Pnp4
