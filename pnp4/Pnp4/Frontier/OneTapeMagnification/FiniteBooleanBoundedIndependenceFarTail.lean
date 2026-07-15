import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFullIndependenceRestriction
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Aggregate high-tail splitting under bounded independence

Full independence diagonalizes the whole high-degree Fourier tail, but costs
an exponentially large seed space.  The concrete structured DPTW source has a
short seed and exact `(4m+1)`-wise laws in both halves.  This file records the
strongest aggregate statement that follows from those bounded-independence
laws alone.

For arbitrary Fourier supports, the restricted-character pair moment factors
as

`E_D chi_(S triangle R)(D) * E_T 1[T is zero on S union R]`.

Consequently a `q`-wise unbiased base kills every distinct pair with
`|(S triangle R)| <= q`.  The high-tail second moment is exactly a diagonal
term plus a single explicit far residual over pairs with
`|(S triangle R)| > q`.  A `q`-wise mask law controls the diagonal even when a
support is larger than `q`, by restricting to a `q`-element subset.

The far residual is bounded generically by `p^q` times a Fourier-`ℓ₁` square.
Bounded independence alone does not turn that into a size-free `ℓ₂` estimate:
eliminating the remaining loss needs additional algebra of the concrete
finite-field source or a selector-specific signed estimate.
-/

namespace FiniteBooleanBoundedIndependenceFarTail

open scoped BigOperators symmDiff
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanFourierEnergy
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanFullIndependenceRestriction
open FiniteUnambiguousFBDD
open DPTWStructuredFieldCoordinatePrimitive

/-! ## Arbitrary-support restricted-character pairs -/

/-- Freezing both supports is the same event as freezing their union. -/
@[simp]
theorem maskAllZeroIndicator_mul_eq_union {n : Nat}
    (left right : Finset (Fin n)) (mask : Fin n → Bool) :
    maskAllZeroIndicator left mask * maskAllZeroIndicator right mask =
      maskAllZeroIndicator (left ∪ right) mask := by
  unfold maskAllZeroIndicator
  by_cases hleft : ∀ index ∈ left, mask index = false
  · by_cases hright : ∀ index ∈ right, mask index = false
    · have hunion : ∀ index ∈ left ∪ right, mask index = false := by
        intro index hindex
        rcases Finset.mem_union.mp hindex with hindex | hindex
        · exact hleft index hindex
        · exact hright index hindex
      rw [if_pos hleft, if_pos hright, if_pos hunion]
      norm_num
    · have hunion : ¬ ∀ index ∈ left ∪ right, mask index = false := by
        intro hall
        apply hright
        intro index hindex
        exact hall index (Finset.mem_union_right left hindex)
      rw [if_pos hleft, if_neg hright, if_neg hunion]
      norm_num
  · have hunion : ¬ ∀ index ∈ left ∪ right, mask index = false := by
      intro hall
      apply hleft
      intro index hindex
      exact hall index (Finset.mem_union_left right hindex)
    rw [if_neg hleft, if_neg hunion]
    simp

/-- Exact factorization of an arbitrary pair of restricted characters. -/
theorem restrictedCharacterAverage_pairMoment_eq {n : Nat}
    {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (left right : Finset (Fin n)) :
    finiteAverage (fun seed : DSeed × TSeed =>
      restrictedCharacterAverage left (D seed.1) (T seed.2) *
        restrictedCharacterAverage right (D seed.1) (T seed.2)) =
      finiteAverage (fun d : DSeed => character (left ∆ right) (D d)) *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator (left ∪ right) (T t)) := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        restrictedCharacterAverage left (D seed.1) (T seed.2) *
          restrictedCharacterAverage right (D seed.1) (T seed.2)) =
      finiteAverage (fun d : DSeed =>
        character left (D d) * character right (D d)) *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator left (T t) *
            maskAllZeroIndicator right (T t)) := by
      rw [← finiteAverage_prod_mul]
      apply finiteAverage_congr
      intro seed
      rw [restrictedCharacterAverage_eq, restrictedCharacterAverage_eq]
      ring
    _ = finiteAverage (fun d : DSeed =>
          character (left ∆ right) (D d)) *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator (left ∪ right) (T t)) := by
      congr 1
      · apply finiteAverage_congr
        intro d
        exact character_mul_character_eq_symmDiff left right (D d)
      · apply finiteAverage_congr
        intro t
        exact maskAllZeroIndicator_mul_eq_union left right (T t)

@[simp]
theorem abs_boolSign_eq_one (value : Bool) :
    |FiniteBooleanFourier.boolSign value| = 1 := by
  cases value <;> norm_num

@[simp]
theorem abs_character_eq_one {n : Nat} (support : Finset (Fin n))
    (input : Fin n → Bool) :
    |character support input| = 1 := by
  classical
  unfold character
  rw [Finset.abs_prod]
  simp

/-- Every Walsh character has finite-average magnitude at most one. -/
theorem abs_character_average_le_one
    {n : Nat} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (source : Seed → Fin n → Bool) (support : Finset (Fin n)) :
    |finiteAverage (fun seed : Seed => character support (source seed))| ≤ 1 := by
  exact abs_finiteAverage_le_of_pointwise_abs_le _ 1 fun seed => by
    rw [abs_character_eq_one]

/-- A bounded unbiased pattern law kills every nonempty character within its
query budget. -/
theorem character_pair_average_eq_zero_of_patternUnbiased
    {n q : Nat} {DSeed : Type*} [Fintype DSeed] [Nonempty DSeed]
    (D : DSeed → Fin n → Bool) (hD : IsKWisePatternUnbiased q D)
    (left right : Finset (Fin n)) (hne : left ≠ right)
    (hcard : (left ∆ right).card ≤ q) :
    finiteAverage (fun d : DSeed =>
      character (left ∆ right) (D d)) = 0 := by
  exact character_average_eq_zero_of_patternUnbiased
    D hD (left ∆ right) hcard (Finset.symmDiff_nonempty.mpr hne)

/-- Exact mask survival for any support within the bounded-independence
budget. -/
theorem maskAllZeroIndicator_average_eq_pow_of_patternFalseBiased
    {n q : Nat} {TSeed : Type*} [Fintype TSeed] [Nonempty TSeed]
    (T : TSeed → Fin n → Bool) (p : ℚ)
    (hT : IsKWisePatternFalseBiased q p T)
    (support : Finset (Fin n)) (hcard : support.card ≤ q) :
    finiteAverage (fun t : TSeed => maskAllZeroIndicator support (T t)) =
      p ^ support.card := by
  calc
    finiteAverage (fun t : TSeed => maskAllZeroIndicator support (T t)) =
      finiteAverage (fun t : TSeed =>
        localPatternIndicator support (allFalseAssignment support) (T t)) := by
          apply finiteAverage_congr
          intro t
          exact
            (localPatternIndicator_allFalse_eq_maskAllZeroIndicator
              support (T t)).symm
    _ = localPatternProductMass p (allFalseAssignment support) :=
      hT support hcard (allFalseAssignment support)
    _ = p ^ support.card := localPatternProductMass_allFalse support p

/-- Freezing a larger support implies freezing every smaller support. -/
theorem maskAllZeroIndicator_le_of_subset {n : Nat}
    {small large : Finset (Fin n)} (hsubset : small ⊆ large)
    (mask : Fin n → Bool) :
    maskAllZeroIndicator large mask ≤ maskAllZeroIndicator small mask := by
  unfold maskAllZeroIndicator
  by_cases hlarge : ∀ index ∈ large, mask index = false
  · have hsmall : ∀ index ∈ small, mask index = false := by
      intro index hindex
      exact hlarge index (hsubset hindex)
    rw [if_pos hlarge, if_pos hsmall]
  · by_cases hsmall : ∀ index ∈ small, mask index = false
    · rw [if_neg hlarge, if_pos hsmall]
      norm_num
    · rw [if_neg hlarge, if_neg hsmall]

/-- A `q`-wise mask law bounds survival of an arbitrarily large support by
the probability of freezing any chosen `lower`-element subset. -/
theorem maskAllZeroIndicator_average_le_pow_of_cardLowerBound
    {n q lower : Nat} {TSeed : Type*}
    [Fintype TSeed] [Nonempty TSeed]
    (T : TSeed → Fin n → Bool) (p : ℚ)
    (hT : IsKWisePatternFalseBiased q p T)
    (support : Finset (Fin n))
    (hlowerQ : lower ≤ q) (hlowerSupport : lower ≤ support.card) :
    finiteAverage (fun t : TSeed => maskAllZeroIndicator support (T t)) ≤
      p ^ lower := by
  classical
  obtain ⟨small, hsmallSubset, hsmallCard⟩ :=
    Finset.exists_subset_card_eq hlowerSupport
  calc
    finiteAverage (fun t : TSeed => maskAllZeroIndicator support (T t)) ≤
      finiteAverage (fun t : TSeed => maskAllZeroIndicator small (T t)) :=
        finiteAverage_mono fun t =>
          maskAllZeroIndicator_le_of_subset hsmallSubset (T t)
    _ = p ^ small.card :=
      maskAllZeroIndicator_average_eq_pow_of_patternFalseBiased
        T p hT small (hsmallCard.le.trans hlowerQ)
    _ = p ^ lower := by rw [hsmallCard]

/-- Even for a far pair, the mask half of its pair kernel is bounded by
`p^q`: the symmetric difference is contained in the union, so the union has
at least `q` coordinates whenever its symmetric difference has more than
`q`.  This does not by itself control the signed Fourier coefficient sum. -/
theorem farPair_maskAllZeroIndicator_average_le_pow
    {n q : Nat} {TSeed : Type*} [Fintype TSeed] [Nonempty TSeed]
    (T : TSeed → Fin n → Bool) (p : ℚ)
    (hT : IsKWisePatternFalseBiased q p T)
    (left right : Finset (Fin n))
    (hfar : q < (left ∆ right).card) :
    finiteAverage (fun t : TSeed ↦
      maskAllZeroIndicator (left ∪ right) (T t)) ≤ p ^ q := by
  apply maskAllZeroIndicator_average_le_pow_of_cardLowerBound
    T p hT (left ∪ right) (Nat.le_refl q)
  exact (Nat.le_of_lt hfar).trans
    (Finset.card_le_card Finset.symmDiff_subset_union)

/-- The complete restricted-character kernel of a far pair has magnitude at
most `p^q`.  The base character average contributes at most one, while the
mask survival contributes `p^q`. -/
theorem abs_restrictedCharacterAverage_pairMoment_le_pow_of_far
    {n q : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool) (p : ℚ)
    (hT : IsKWisePatternFalseBiased q p T)
    (left right : Finset (Fin n)) (hfar : q < (left ∆ right).card) :
    |finiteAverage (fun seed : DSeed × TSeed =>
      restrictedCharacterAverage left (D seed.1) (T seed.2) *
        restrictedCharacterAverage right (D seed.1) (T seed.2))| ≤
      p ^ q := by
  rw [restrictedCharacterAverage_pairMoment_eq D T left right]
  have hmaskNonnegative :
      0 ≤ finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator (left ∪ right) (T t)) := by
    apply finiteAverage_nonneg
    intro t
    unfold maskAllZeroIndicator
    split <;> norm_num
  calc
    |finiteAverage (fun d : DSeed => character (left ∆ right) (D d)) *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator (left ∪ right) (T t))| =
      |finiteAverage (fun d : DSeed => character (left ∆ right) (D d))| *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator (left ∪ right) (T t)) := by
            rw [abs_mul, abs_of_nonneg hmaskNonnegative]
    _ ≤ 1 * finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator (left ∪ right) (T t)) := by
            apply mul_le_mul_of_nonneg_right
            · exact abs_character_average_le_one D (left ∆ right)
            · exact hmaskNonnegative
    _ = finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator (left ∪ right) (T t)) := one_mul _
    _ ≤ p ^ q := farPair_maskAllZeroIndicator_average_le_pow
      T p hT left right hfar

/-! ## Exact diagonal/far split -/

/-- Pair moment retained only when the symmetric-difference character lies
outside the unbiasedness budget. -/
noncomputable def highTailFarPairCorrelation
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    (f : (Fin n → Bool) → ℚ) (cutoff q : Nat)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool) : ℚ :=
  ∑ left ∈ highDegreeSupports n cutoff,
    ∑ right ∈ highDegreeSupports n cutoff,
      if left ≠ right ∧ q < (left ∆ right).card then
        coefficient f left * coefficient f right *
          finiteAverage (fun seed : DSeed × TSeed =>
            restrictedCharacterAverage left (D seed.1) (T seed.2) *
              restrictedCharacterAverage right (D seed.1) (T seed.2))
      else 0

/-- Fourier `ℓ₁` mass of the supports strictly above `cutoff`. -/
noncomputable def highTailCoefficientL1 {n : Nat}
    (f : (Fin n → Bool) → ℚ) (cutoff : Nat) : ℚ :=
  ∑ support ∈ highDegreeSupports n cutoff, |coefficient f support|

/-- Bounded independence gives an unconditional `p^q` kernel bound on every
far pair.  Summing absolute values therefore controls the entire far residual
by the square of the high-tail Fourier `ℓ₁` mass.  This generic bound also
overcounts non-far pairs, but exposes the real norm mismatch: Parseval controls
`ℓ₂`, not this `ℓ₁` quantity. -/
theorem abs_highTailFarPairCorrelation_le_pow_mul_l1_sq
    {n q cutoff : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp0 : 0 ≤ p) (hT : IsKWisePatternFalseBiased q p T) :
    |highTailFarPairCorrelation f cutoff q D T| ≤
      p ^ q * (highTailCoefficientL1 f cutoff) ^ 2 := by
  classical
  unfold highTailFarPairCorrelation highTailCoefficientL1
  let supports := highDegreeSupports n cutoff
  calc
    |∑ left ∈ supports, ∑ right ∈ supports,
        if left ≠ right ∧ q < (left ∆ right).card then
          coefficient f left * coefficient f right *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage left (D seed.1) (T seed.2) *
                restrictedCharacterAverage right (D seed.1) (T seed.2))
        else 0| ≤
      ∑ left ∈ supports, |∑ right ∈ supports,
        if left ≠ right ∧ q < (left ∆ right).card then
          coefficient f left * coefficient f right *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage left (D seed.1) (T seed.2) *
                restrictedCharacterAverage right (D seed.1) (T seed.2))
        else 0| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ left ∈ supports, ∑ right ∈ supports,
        |if left ≠ right ∧ q < (left ∆ right).card then
          coefficient f left * coefficient f right *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage left (D seed.1) (T seed.2) *
                restrictedCharacterAverage right (D seed.1) (T seed.2))
        else 0| := by
          apply Finset.sum_le_sum
          intro left _
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ left ∈ supports, ∑ right ∈ supports,
        |coefficient f left| * |coefficient f right| * p ^ q := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          by_cases hfar : left ≠ right ∧ q < (left ∆ right).card
          · rw [if_pos hfar, abs_mul, abs_mul]
            apply mul_le_mul_of_nonneg_left
            · exact abs_restrictedCharacterAverage_pairMoment_le_pow_of_far
                D T p hT left right hfar.2
            · positivity
          · rw [if_neg hfar, abs_zero]
            positivity
    _ = p ^ q * ∑ left ∈ supports, ∑ right ∈ supports,
        |coefficient f left| * |coefficient f right| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro left _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro right _
          ring
    _ = p ^ q *
        ((∑ left ∈ supports, |coefficient f left|) *
          ∑ right ∈ supports, |coefficient f right|) := by
            rw [Finset.sum_mul_sum]
    _ = p ^ q *
        (∑ support ∈ supports, |coefficient f support|) ^ 2 := by
          rw [pow_two]

/-- Bounded unbiasedness splits an arbitrary restricted-character Gram entry
into its diagonal and an explicit far off-diagonal residual. -/
theorem restrictedCharacterAverage_pairMoment_eq_diagonal_add_far
    {n q : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased q D)
    (left right : Finset (Fin n)) :
    finiteAverage (fun seed : DSeed × TSeed =>
      restrictedCharacterAverage left (D seed.1) (T seed.2) *
        restrictedCharacterAverage right (D seed.1) (T seed.2)) =
      (if left = right then
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator left (T t))
      else 0) +
      (if left ≠ right ∧ q < (left ∆ right).card then
        finiteAverage (fun seed : DSeed × TSeed =>
          restrictedCharacterAverage left (D seed.1) (T seed.2) *
            restrictedCharacterAverage right (D seed.1) (T seed.2))
      else 0) := by
  by_cases heq : left = right
  · subst right
    rw [if_pos rfl]
    simp only [ne_eq, not_true_eq_false, false_and, if_false, add_zero]
    calc
      finiteAverage (fun seed : DSeed × TSeed =>
          restrictedCharacterAverage left (D seed.1) (T seed.2) *
            restrictedCharacterAverage left (D seed.1) (T seed.2)) =
        finiteAverage (fun d : DSeed =>
            character (left ∆ left) (D d)) *
          finiteAverage (fun t : TSeed =>
            maskAllZeroIndicator (left ∪ left) (T t)) :=
              restrictedCharacterAverage_pairMoment_eq D T left left
      _ = finiteAverage (fun t : TSeed =>
            maskAllZeroIndicator left (T t)) := by simp
  · rw [if_neg heq]
    by_cases hfar : q < (left ∆ right).card
    · simp [heq, hfar]
    · have hcard : (left ∆ right).card ≤ q := Nat.le_of_not_gt hfar
      have hzero :
          finiteAverage (fun seed : DSeed × TSeed =>
            restrictedCharacterAverage left (D seed.1) (T seed.2) *
              restrictedCharacterAverage right (D seed.1) (T seed.2)) = 0 := by
        rw [restrictedCharacterAverage_pairMoment_eq D T left right]
        rw [character_pair_average_eq_zero_of_patternUnbiased
          D hD left right heq hcard]
        simp
      simp [heq, hfar, hzero]

/-- Exact arbitrary-source pair expansion of the aggregate high-tail second
moment. -/
theorem highTail_restriction_secondMoment_eq_sum_pairMoments
    {n cutoff : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail f cutoff
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      ∑ left ∈ highDegreeSupports n cutoff,
        ∑ right ∈ highDegreeSupports n cutoff,
          coefficient f left * coefficient f right *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage left (D seed.1) (T seed.2) *
                restrictedCharacterAverage right (D seed.1) (T seed.2)) := by
  classical
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail f cutoff
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (∑ left ∈ highDegreeSupports n cutoff,
            coefficient f left *
              restrictedCharacterAverage left (D seed.1) (T seed.2)) *
          (∑ right ∈ highDegreeSupports n cutoff,
            coefficient f right *
              restrictedCharacterAverage right (D seed.1) (T seed.2))) := by
        apply finiteAverage_congr
        intro seed
        rw [finiteAverage_ratHighDegreeFourierTail_masked]
        rw [pow_two]
    _ = finiteAverage (fun seed : DSeed × TSeed =>
        ∑ left ∈ highDegreeSupports n cutoff,
          ∑ right ∈ highDegreeSupports n cutoff,
            (coefficient f left *
                restrictedCharacterAverage left (D seed.1) (T seed.2)) *
              (coefficient f right *
                restrictedCharacterAverage right (D seed.1) (T seed.2))) := by
      apply finiteAverage_congr
      intro seed
      rw [Finset.sum_mul_sum]
    _ = ∑ left ∈ highDegreeSupports n cutoff,
        ∑ right ∈ highDegreeSupports n cutoff,
          finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient f left *
                restrictedCharacterAverage left (D seed.1) (T seed.2)) *
              (coefficient f right *
                restrictedCharacterAverage right (D seed.1) (T seed.2))) := by
      rw [finiteAverage_finset_sum]
      apply Finset.sum_congr rfl
      intro left _
      rw [finiteAverage_finset_sum]
    _ = ∑ left ∈ highDegreeSupports n cutoff,
        ∑ right ∈ highDegreeSupports n cutoff,
          coefficient f left * coefficient f right *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage left (D seed.1) (T seed.2) *
                restrictedCharacterAverage right (D seed.1) (T seed.2)) := by
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      calc
        finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient f left *
                restrictedCharacterAverage left (D seed.1) (T seed.2)) *
              (coefficient f right *
                restrictedCharacterAverage right (D seed.1) (T seed.2))) =
          finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient f left * coefficient f right) *
              (restrictedCharacterAverage left (D seed.1) (T seed.2) *
                restrictedCharacterAverage right
                  (D seed.1) (T seed.2))) := by
            apply finiteAverage_congr
            intro seed
            ring
        _ = (coefficient f left * coefficient f right) *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage left (D seed.1) (T seed.2) *
                restrictedCharacterAverage right
                  (D seed.1) (T seed.2)) :=
          finiteAverage_const_mul _ _

/-- Exact aggregate split: bounded independence controls the diagonal and all
near off-diagonal pairs; only the displayed far Walsh correlation remains. -/
theorem highTail_restriction_secondMoment_eq_diagonal_add_far
    {n cutoff q : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased q D) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail f cutoff
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      (∑ support ∈ highDegreeSupports n cutoff,
        (coefficient f support) ^ 2 *
          finiteAverage (fun t : TSeed =>
            maskAllZeroIndicator support (T t))) +
        highTailFarPairCorrelation f cutoff q D T := by
  classical
  rw [highTail_restriction_secondMoment_eq_sum_pairMoments f D T]
  unfold highTailFarPairCorrelation
  calc
    (∑ left ∈ highDegreeSupports n cutoff,
        ∑ right ∈ highDegreeSupports n cutoff,
          coefficient f left * coefficient f right *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage left (D seed.1) (T seed.2) *
                restrictedCharacterAverage right (D seed.1) (T seed.2))) =
      (∑ left ∈ highDegreeSupports n cutoff,
        ∑ right ∈ highDegreeSupports n cutoff,
          coefficient f left * coefficient f right *
            (if left = right then
              finiteAverage (fun t : TSeed =>
                maskAllZeroIndicator left (T t))
            else 0)) +
      (∑ left ∈ highDegreeSupports n cutoff,
        ∑ right ∈ highDegreeSupports n cutoff,
          if left ≠ right ∧ q < (left ∆ right).card then
            coefficient f left * coefficient f right *
              finiteAverage (fun seed : DSeed × TSeed =>
                restrictedCharacterAverage left (D seed.1) (T seed.2) *
                  restrictedCharacterAverage right
                    (D seed.1) (T seed.2))
          else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro left _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro right _
        rw [restrictedCharacterAverage_pairMoment_eq_diagonal_add_far
          D T hD left right]
        by_cases heq : left = right
        · simp [heq]
        · by_cases hfar : q < (left ∆ right).card
          · simp [heq, hfar]
          · simp [heq, hfar]
    _ = (∑ support ∈ highDegreeSupports n cutoff,
          finiteAverage (fun t : TSeed =>
            maskAllZeroIndicator support (T t)) *
              (coefficient f support) ^ 2) +
        (∑ left ∈ highDegreeSupports n cutoff,
          ∑ right ∈ highDegreeSupports n cutoff,
            if left ≠ right ∧ q < (left ∆ right).card then
              coefficient f left * coefficient f right *
                finiteAverage (fun seed : DSeed × TSeed =>
                  restrictedCharacterAverage left (D seed.1) (T seed.2) *
                    restrictedCharacterAverage right
                      (D seed.1) (T seed.2))
            else 0) := by
      congr 1
      exact sum_mul_ite_eq_weighted_diagonal
        (highDegreeSupports n cutoff) (coefficient f)
        (fun support => finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator support (T t)))
    _ = (∑ support ∈ highDegreeSupports n cutoff,
          (coefficient f support) ^ 2 *
            finiteAverage (fun t : TSeed =>
              maskAllZeroIndicator support (T t))) +
        (∑ left ∈ highDegreeSupports n cutoff,
          ∑ right ∈ highDegreeSupports n cutoff,
            if left ≠ right ∧ q < (left ∆ right).card then
              coefficient f left * coefficient f right *
                finiteAverage (fun seed : DSeed × TSeed =>
                  restrictedCharacterAverage left (D seed.1) (T seed.2) *
                    restrictedCharacterAverage right
                      (D seed.1) (T seed.2))
            else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro support _
      ring

/-! ## Cardinality-free control of the diagonal -/

/-- A bounded mask law controls the whole diagonal high-tail energy without
any factor depending on the number of Fourier supports.  Only
`cutoff + 1` queried coordinates are needed from each high support. -/
theorem highTail_diagonalEnergy_le_pow_succ
    {n cutoff q : Nat} {TSeed : Type*}
    [Fintype TSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (T : TSeed → Fin n → Bool) (p : ℚ)
    (hp0 : 0 ≤ p)
    (hcutoffQ : cutoff + 1 ≤ q)
    (hT : IsKWisePatternFalseBiased q p T)
    (hbounded : ∀ input, |f input| ≤ 1) :
    (∑ support ∈ highDegreeSupports n cutoff,
      (coefficient f support) ^ 2 *
        finiteAverage (fun t : TSeed ↦
          maskAllZeroIndicator support (T t))) ≤
      p ^ (cutoff + 1) := by
  calc
    (∑ support ∈ highDegreeSupports n cutoff,
        (coefficient f support) ^ 2 *
          finiteAverage (fun t : TSeed ↦
            maskAllZeroIndicator support (T t))) ≤
      ∑ support ∈ highDegreeSupports n cutoff,
        (coefficient f support) ^ 2 * p ^ (cutoff + 1) := by
          apply Finset.sum_le_sum
          intro support hsupport
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact maskAllZeroIndicator_average_le_pow_of_cardLowerBound
            T p hT support hcutoffQ
              (by
                have := mem_highDegreeSupports.mp hsupport
                omega)
    _ = p ^ (cutoff + 1) *
        ∑ support ∈ highDegreeSupports n cutoff,
          (coefficient f support) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro support _
      ring
    _ ≤ p ^ (cutoff + 1) *
        ∑ support : Finset (Fin n),
          (coefficient f support) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp0 _)
      exact Finset.sum_le_univ_sum_of_nonneg fun support ↦
        sq_nonneg (coefficient f support)
    _ = p ^ (cutoff + 1) *
        finiteAverage (fun input : Fin n → Bool ↦ (f input) ^ 2) := by
      rw [parseval]
    _ ≤ p ^ (cutoff + 1) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact finiteAverage_sq_le_one_of_abs_le_one f hbounded
      · exact pow_nonneg hp0 _
    _ = p ^ (cutoff + 1) := mul_one _

/-- Under bounded independence, the aggregate high-tail second moment is at
most the size-free diagonal bound plus the absolute value of the one
remaining far Walsh residual. -/
theorem highTail_restriction_secondMoment_le_pow_succ_add_abs_far
    {n cutoff q : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp0 : 0 ≤ p)
    (hcutoffQ : cutoff + 1 ≤ q)
    (hD : IsKWisePatternUnbiased q D)
    (hT : IsKWisePatternFalseBiased q p T)
    (hbounded : ∀ input, |f input| ≤ 1) :
    finiteAverage (fun seed : DSeed × TSeed ↦
      (finiteAverage (fun uniform : Fin n → Bool ↦
        ratHighDegreeFourierTail f cutoff
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) ≤
      p ^ (cutoff + 1) +
        |highTailFarPairCorrelation f cutoff q D T| := by
  rw [highTail_restriction_secondMoment_eq_diagonal_add_far f D T hD]
  exact add_le_add
    (highTail_diagonalEnergy_le_pow_succ
      f T p hp0 hcutoffQ hT hbounded)
    (le_abs_self (highTailFarPairCorrelation f cutoff q D T))

/-- Fully explicit unconditional version of the bounded-independence bound.
The remaining far term is paid for by its exact kernel scale `p^q` and the
square of the high-tail Fourier `ℓ₁` mass. -/
theorem highTail_restriction_secondMoment_le_pow_succ_add_pow_mul_l1_sq
    {n cutoff q : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp0 : 0 ≤ p)
    (hcutoffQ : cutoff + 1 ≤ q)
    (hD : IsKWisePatternUnbiased q D)
    (hT : IsKWisePatternFalseBiased q p T)
    (hbounded : ∀ input, |f input| ≤ 1) :
    finiteAverage (fun seed : DSeed × TSeed ↦
      (finiteAverage (fun uniform : Fin n → Bool ↦
        ratHighDegreeFourierTail f cutoff
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) ≤
      p ^ (cutoff + 1) +
        p ^ q * (highTailCoefficientL1 f cutoff) ^ 2 := by
  calc
    finiteAverage (fun seed : DSeed × TSeed ↦
        (finiteAverage (fun uniform : Fin n → Bool ↦
          ratHighDegreeFourierTail f cutoff
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) ≤
      p ^ (cutoff + 1) +
        |highTailFarPairCorrelation f cutoff q D T| :=
          highTail_restriction_secondMoment_le_pow_succ_add_abs_far
            f D T p hp0 hcutoffQ hD hT hbounded
    _ ≤ p ^ (cutoff + 1) +
        p ^ q * (highTailCoefficientL1 f cutoff) ^ 2 :=
      add_le_add_left
        (abs_highTailFarPairCorrelation_le_pow_mul_l1_sq
          f D T p hp0 hT) _

/-! ## Concrete structured-source specialization -/

/-- The actual finite-field coordinate primitives give a `(4m+1)`-wise
diagonal/far decomposition at cutoff `2m`.  Thus their aggregate high-tail
second moment has the size-free diagonal bound `p^(2m+1)`.  The far residual
has a `p^(4m+1)` Fourier-`ℓ₁` bound, but no size-free `ℓ₂` bound follows from
the pattern laws alone. -/
theorem structured_highTail_restriction_secondMoment_le_pow_succ_add_abs_far
    (d m tailBits : Nat) (hd : 0 < d) (htail : tailBits ≤ d)
    (f : (Fin (2 ^ d) → Bool) → ℚ)
    (hbounded : ∀ input, |f input| ≤ 1) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * d) ×
          FiniteBitTape (structuredIndependence m * d) ↦
      (finiteAverage (fun uniform : Fin (2 ^ d) → Bool ↦
        ratHighDegreeFourierTail f (2 * m)
          (maskedInput
            ((structuredUnbiasedPrimitive d m hd).generate seed.1)
            ((structuredDyadicPrimitive d m tailBits hd htail).generate seed.2)
            uniform))) ^ 2) ≤
      (1 / (2 : ℚ) ^ tailBits) ^ (2 * m + 1) +
        |highTailFarPairCorrelation f (2 * m) (structuredIndependence m)
          (structuredUnbiasedPrimitive d m hd).generate
          (structuredDyadicPrimitive d m tailBits hd htail).generate| := by
  apply highTail_restriction_secondMoment_le_pow_succ_add_abs_far
  · positivity
  · unfold structuredIndependence
    omega
  · exact structuredUnbiasedPrimitive_patternUnbiased d m hd
  · exact structuredDyadicPrimitive_patternFalseBiased
      d m tailBits hd htail
  · exact hbounded

/-- Explicit structured-source corollary: all unaccounted far correlations
are bounded by `p^(4m+1)` times the squared high-tail Fourier `ℓ₁` mass. -/
theorem structured_highTail_restriction_secondMoment_le_pow_succ_add_pow_mul_l1_sq
    (d m tailBits : Nat) (hd : 0 < d) (htail : tailBits ≤ d)
    (f : (Fin (2 ^ d) → Bool) → ℚ)
    (hbounded : ∀ input, |f input| ≤ 1) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * d) ×
          FiniteBitTape (structuredIndependence m * d) ↦
      (finiteAverage (fun uniform : Fin (2 ^ d) → Bool ↦
        ratHighDegreeFourierTail f (2 * m)
          (maskedInput
            ((structuredUnbiasedPrimitive d m hd).generate seed.1)
            ((structuredDyadicPrimitive d m tailBits hd htail).generate seed.2)
            uniform))) ^ 2) ≤
      (1 / (2 : ℚ) ^ tailBits) ^ (2 * m + 1) +
        (1 / (2 : ℚ) ^ tailBits) ^ structuredIndependence m *
          (highTailCoefficientL1 f (2 * m)) ^ 2 := by
  apply highTail_restriction_secondMoment_le_pow_succ_add_pow_mul_l1_sq
  · positivity
  · unfold structuredIndependence
    omega
  · exact structuredUnbiasedPrimitive_patternUnbiased d m hd
  · exact structuredDyadicPrimitive_patternFalseBiased
      d m tailBits hd htail
  · exact hbounded

end FiniteBooleanBoundedIndependenceFarTail

end OneTapeMagnification
end Frontier
end Pnp4
