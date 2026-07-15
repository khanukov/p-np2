import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredMaskRank
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDOneRoundFoolingBound
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Full-field correlation of the structured DPTW mask

When every chosen-basis coordinate is used by the structured dyadic mask,
the false set is the singleton zero of `GF(2^n)`.  A nonzero polynomial of
degree below `k` cannot therefore freeze `k` distinct field points.  At the
cutoff used by the DPTW pair, every dual far pair survives only for the zero
polynomial.

This gives a size-free bound on the remaining signed dual-code correlation.
The full-field choice has a separate multiround survivor cost and is not by
itself a small-threshold lower bound.
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
open DPTWFiniteFieldKWiseSeed
open GaloisBilinearTensorBridge
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank

namespace DPTWStructuredFullFieldCorrelation

/-- Vanishing of all chosen-basis coordinates is equality to zero in the
binary extension field. -/
theorem mem_zeroPrefixFalseSet_full_iff
    (n : Nat) (hn : 0 < n) (value : GaloisField 2 n) :
    value ∈ zeroPrefixFalseSet n n (Nat.ne_of_gt hn) (by omega) ↔
      value = 0 := by
  rw [mem_zeroPrefixFalseSet]
  constructor
  · intro hcoordinates
    apply (gfTwoBoolCoordinates n (Nat.ne_of_gt hn)).injective
    funext coordinate
    simpa [prefixPosition] using hcoordinates coordinate
  · rintro rfl coordinate
    simp

/-- With the full chosen-basis prefix, the polynomial mask is false at a
node exactly when the polynomial evaluates to zero there. -/
theorem polynomialSubsetSource_full_eq_false_iff
    (n k : Nat) (hn : 0 < n)
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k)
    (index : Fin (2 ^ n)) :
    polynomialSubsetSource
          (structuredTruthTableNode n (Nat.ne_of_gt hn)) k
          (zeroPrefixFalseSet n n (Nat.ne_of_gt hn) (by omega))
          polynomial index = false ↔
      polynomial.1.eval
          (structuredTruthTableNode n (Nat.ne_of_gt hn) index) = 0 := by
  rw [polynomialSubsetSource, fieldSubsetCoin_eq_false_iff,
    mem_zeroPrefixFalseSet_full_iff n hn]

/-- A degree-`< k` polynomial which vanishes on at least `k` distinct
structured truth-table nodes is the zero polynomial. -/
theorem degreeLT_eq_zero_of_vanishes_on_structuredSupport
    (n k : Nat) (hn : 0 < n)
    (support : Finset (Fin (2 ^ n)))
    (hcard : k ≤ support.card)
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k)
    (hvanish : ∀ index ∈ support,
      polynomial.1.eval
        (structuredTruthTableNode n (Nat.ne_of_gt hn) index) = 0) :
    polynomial = 0 := by
  apply Subtype.ext
  by_contra hnonzero
  let nodes : Finset (GaloisField 2 n) :=
    support.image (structuredTruthTableNode n (Nat.ne_of_gt hn))
  have hnodesCard : nodes.card = support.card := by
    exact Finset.card_image_of_injective support
      (structuredTruthTableNode_injective n (Nat.ne_of_gt hn))
  have hnodesRoots : nodes ⊆ polynomial.1.roots.toFinset := by
    intro value hvalue
    rw [Finset.mem_image] at hvalue
    obtain ⟨index, hindex, rfl⟩ := hvalue
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hnonzero]
    exact hvanish index hindex
  have hrootsCard : nodes.card ≤ polynomial.1.natDegree := by
    calc
      nodes.card ≤ polynomial.1.roots.toFinset.card :=
        Finset.card_le_card hnodesRoots
      _ ≤ polynomial.1.roots.card := Multiset.toFinset_card_le _
      _ ≤ polynomial.1.natDegree := Polynomial.card_roots' _
  have hdegree : polynomial.1.natDegree < k :=
    (Polynomial.natDegree_lt_iff_degree_lt hnonzero).2
      (Polynomial.mem_degreeLT.mp polynomial.2)
  omega

/-! ## Low-degree isometry on the structured base source -/

/-- Fourier supports of degree at most `cutoff`. -/
def lowDegreeSupports (n cutoff : Nat) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun support => support.card ≤ cutoff)

@[simp]
theorem mem_lowDegreeSupports {n cutoff : Nat}
    {support : Finset (Fin n)} :
    support ∈ lowDegreeSupports n cutoff ↔ support.card ≤ cutoff := by
  simp [lowDegreeSupports]

/-- The low-degree Fourier projection, including its constant term. -/
noncomputable def ratLowDegreeFourierPart {n : Nat}
    (f : (Fin n → Bool) → Rat) (cutoff : Nat)
    (input : Fin n → Bool) : Rat :=
  ∑ support ∈ lowDegreeSupports n cutoff,
    coefficient f support * character support input

/-- Fourier inversion splits exactly into the low projection and the strict
high tail. -/
theorem ratHighDegreeFourierTail_eq_sub_lowDegreePart
    {n cutoff : Nat} (f : (Fin n → Bool) → Rat)
    (input : Fin n → Bool) :
    ratHighDegreeFourierTail f cutoff input =
      f input - ratLowDegreeFourierPart f cutoff input := by
  classical
  rw [ratHighDegreeFourierTail_eq_sum_highDegreeSupports,
    ← fourier_inversion f input]
  unfold ratLowDegreeFourierPart lowDegreeSupports highDegreeSupports
  have hsplit := Finset.sum_filter_not_add_sum_filter
    (Finset.univ : Finset (Finset (Fin n)))
    (fun support => cutoff < support.card)
    (fun support => coefficient f support * character support input)
  simp only [Finset.sum_filter, Nat.not_lt] at hsplit ⊢
  linarith

/-- A `q`-wise unbiased source is an exact isometry on Fourier polynomials
of degree at most `cutoff` when `2 * cutoff ≤ q`. -/
theorem lowDegreeFourierPart_secondMoment_eq_energy
    {n cutoff q : Nat} {DSeed : Type*}
    [Fintype DSeed] [Nonempty DSeed]
    (f : (Fin n → Bool) → Rat)
    (D : DSeed → Fin n → Bool)
    (hcutoff : 2 * cutoff ≤ q)
    (hD : IsKWisePatternUnbiased q D) :
    finiteAverage (fun seed : DSeed =>
      (ratLowDegreeFourierPart f cutoff (D seed)) ^ 2) =
      ∑ support ∈ lowDegreeSupports n cutoff,
        (coefficient f support) ^ 2 := by
  classical
  let supports := lowDegreeSupports n cutoff
  calc
    finiteAverage (fun seed : DSeed =>
        (ratLowDegreeFourierPart f cutoff (D seed)) ^ 2) =
      finiteAverage (fun seed : DSeed =>
        ∑ left ∈ supports, ∑ right ∈ supports,
          (coefficient f left * character left (D seed)) *
            (coefficient f right * character right (D seed))) := by
        apply finiteAverage_congr
        intro seed
        unfold ratLowDegreeFourierPart
        rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ left ∈ supports, ∑ right ∈ supports,
        finiteAverage (fun seed : DSeed =>
          (coefficient f left * character left (D seed)) *
            (coefficient f right * character right (D seed))) := by
      rw [finiteAverage_finset_sum]
      apply Finset.sum_congr rfl
      intro left _
      rw [finiteAverage_finset_sum]
    _ = ∑ left ∈ supports, ∑ right ∈ supports,
        coefficient f left * coefficient f right *
          finiteAverage (fun seed : DSeed =>
            character left (D seed) * character right (D seed)) := by
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      calc
        finiteAverage (fun seed : DSeed =>
            (coefficient f left * character left (D seed)) *
              (coefficient f right * character right (D seed))) =
          finiteAverage (fun seed : DSeed =>
            (coefficient f left * coefficient f right) *
              (character left (D seed) * character right (D seed))) := by
                apply finiteAverage_congr
                intro seed
                ring
        _ = _ := finiteAverage_const_mul _ _
    _ = ∑ support ∈ supports, (coefficient f support) ^ 2 := by
      apply Finset.sum_congr rfl
      intro left hleft
      calc
        (∑ right ∈ supports,
            coefficient f left * coefficient f right *
              finiteAverage (fun seed : DSeed =>
                character left (D seed) * character right (D seed))) =
          ∑ right ∈ supports,
            if right = left then (coefficient f left) ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro right hright
              by_cases heq : right = left
              · subst right
                simp [character_square, pow_two]
              · have hleftCard : left.card ≤ cutoff :=
                    mem_lowDegreeSupports.mp hleft
                have hrightCard : right.card ≤ cutoff :=
                  mem_lowDegreeSupports.mp hright
                have hsymmCard : (left ∆ right).card ≤ q := by
                  calc
                    (left ∆ right).card ≤ (left ∪ right).card :=
                      Finset.card_le_card Finset.symmDiff_subset_union
                    _ ≤ left.card + right.card := Finset.card_union_le _ _
                    _ ≤ 2 * cutoff := by omega
                    _ ≤ q := hcutoff
                have hzero :
                    finiteAverage (fun seed : DSeed =>
                      character left (D seed) * character right (D seed)) =
                        0 := by
                  calc
                    finiteAverage (fun seed : DSeed =>
                        character left (D seed) * character right (D seed)) =
                      finiteAverage (fun seed : DSeed =>
                        character (left ∆ right) (D seed)) := by
                          apply finiteAverage_congr
                          intro seed
                          exact character_mul_character_eq_symmDiff
                            left right (D seed)
                    _ = 0 :=
                      character_pair_average_eq_zero_of_patternUnbiased
                        D hD left right (fun h => heq h.symm) hsymmCard
                rw [hzero]
                simp [heq]
        _ = (coefficient f left) ^ 2 := by simp [hleft]
    _ = _ := rfl

/-- Pointwise comparison passes through a normalized finite average. -/
theorem finiteAverage_le_of_pointwise
    {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    {left right : Seed → Rat}
    (hpointwise : ∀ seed, left seed ≤ right seed) :
    finiteAverage left ≤ finiteAverage right := by
  have hcard : (0 : Rat) < (Fintype.card Seed : Rat) := by
    exact_mod_cast Fintype.card_pos
  unfold finiteAverage
  apply (div_le_div_iff_of_pos_right hcard).2
  exact Finset.sum_le_sum fun seed _ => hpointwise seed

/-- Normalized finite averages are additive. -/
theorem finiteAverage_add_local
    {Seed : Type*} [Fintype Seed]
    (left right : Seed → Rat) :
    finiteAverage (fun seed => left seed + right seed) =
      finiteAverage left + finiteAverage right := by
  unfold finiteAverage
  rw [Finset.sum_add_distrib]
  ring

/-- On the structured base code, the unmasked strict `> 2m` Fourier tail of
any pointwise bounded function has second moment at most four. -/
theorem structured_unmaskedHighTail_secondMoment_le_four
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1) :
    finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
      (ratHighDegreeFourierTail f (2 * m)
        ((structuredUnbiasedPrimitive n m hn).generate seed)) ^ 2) ≤ 4 := by
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let low := ratLowDegreeFourierPart f (2 * m)
  have hlowExact :
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
          (low (D seed)) ^ 2) =
        ∑ support ∈ lowDegreeSupports (2 ^ n) (2 * m),
          (coefficient f support) ^ 2 := by
    apply lowDegreeFourierPart_secondMoment_eq_energy
        (q := structuredIndependence m)
    · unfold structuredIndependence
      omega
    · exact structuredUnbiasedPrimitive_patternUnbiased n m hn
  have hlow :
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        (low (D seed)) ^ 2) ≤ 1 := by
    rw [hlowExact]
    exact (bessel f (lowDegreeSupports (2 ^ n) (2 * m))).trans
      (finiteAverage_sq_le_one_of_abs_le_one f hbounded)
  have hf :
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        (f (D seed)) ^ 2) ≤ 1 := by
    apply finiteAverage_sq_le_one_of_abs_le_one
    intro seed
    exact hbounded (D seed)
  calc
    finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        (ratHighDegreeFourierTail f (2 * m) (D seed)) ^ 2) ≤
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        2 * (f (D seed)) ^ 2 + 2 * (low (D seed)) ^ 2) := by
          apply finiteAverage_le_of_pointwise
          intro seed
          rw [ratHighDegreeFourierTail_eq_sub_lowDegreePart]
          dsimp only [low]
          nlinarith [sq_nonneg (f (D seed) +
            ratLowDegreeFourierPart f (2 * m) (D seed))]
    _ = 2 * finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
          (f (D seed)) ^ 2) +
        2 * finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
          (low (D seed)) ^ 2) := by
      rw [finiteAverage_add_local, finiteAverage_const_mul,
        finiteAverage_const_mul]
    _ ≤ 4 := by linarith

/-! ## The signed far sum as unmasked base-code energy -/

/-- The mask which freezes every coordinate. -/
def allFalseMask {n : Nat} : Unit → Fin n → Bool :=
  fun _ _ => false

/-- With the all-false mask, the generic diagonal/far identity is exactly the
unmasked base-code high-tail energy identity. -/
theorem unmaskedHighTail_secondMoment_eq_diagonal_add_far
    {n cutoff q : Nat} {DSeed : Type*}
    [Fintype DSeed] [Nonempty DSeed]
    (f : (Fin n → Bool) → Rat)
    (D : DSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased q D) :
    finiteAverage (fun seed : DSeed =>
      (ratHighDegreeFourierTail f cutoff (D seed)) ^ 2) =
      (∑ support ∈ highDegreeSupports n cutoff,
        (coefficient f support) ^ 2) +
        highTailFarPairCorrelation f cutoff q D allFalseMask := by
  have hsplit :=
    highTail_restriction_secondMoment_eq_diagonal_add_far
      (cutoff := cutoff) (q := q)
      f D (allFalseMask (n := n)) hD
  have hlhs :
      finiteAverage (fun seed : DSeed × Unit =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail f cutoff
            (maskedInput (D seed.1) (allFalseMask seed.2) uniform))) ^ 2) =
        finiteAverage (fun seed : DSeed =>
          (ratHighDegreeFourierTail f cutoff (D seed)) ^ 2) := by
    calc
      finiteAverage (fun seed : DSeed × Unit =>
          (finiteAverage (fun uniform : Fin n → Bool =>
            ratHighDegreeFourierTail f cutoff
              (maskedInput (D seed.1) (allFalseMask seed.2) uniform))) ^ 2) =
        finiteAverage (fun seed : DSeed × Unit =>
          (ratHighDegreeFourierTail f cutoff (D seed.1)) ^ 2) := by
            apply finiteAverage_congr
            intro seed
            congr 1
            calc
              finiteAverage (fun uniform : Fin n → Bool =>
                  ratHighDegreeFourierTail f cutoff
                    (maskedInput (D seed.1)
                      (allFalseMask seed.2) uniform)) =
                finiteAverage (fun _uniform : Fin n → Bool =>
                  ratHighDegreeFourierTail f cutoff (D seed.1)) := by
                    apply finiteAverage_congr
                    intro uniform
                    congr 2
                    funext coordinate
                    simp [allFalseMask, maskedInput]
              _ = ratHighDegreeFourierTail f cutoff (D seed.1) := by
                simp [finiteAverage]
      _ = finiteAverage (fun seed : DSeed =>
          (ratHighDegreeFourierTail f cutoff (D seed)) ^ 2) := by
        change finiteAverage (fun seed : DSeed × Unit =>
            (fun left : DSeed => fun _right : Unit =>
              (ratHighDegreeFourierTail f cutoff (D left)) ^ 2)
              seed.1 seed.2) = _
        rw [finiteAverage_prod_eq_iterated
          (fun left : DSeed => fun _right : Unit =>
            (ratHighDegreeFourierTail f cutoff (D left)) ^ 2)]
        apply finiteAverage_congr
        intro seed
        simp [finiteAverage]
  rw [hlhs] at hsplit
  simpa [allFalseMask, maskAllZeroIndicator, finiteAverage] using hsplit

/-- Equivalently, the signed all-false far sum is high-tail base-code energy
minus ordinary diagonal Fourier energy. -/
theorem allFalse_highTailFarPairCorrelation_eq_sub_diagonal
    {n cutoff q : Nat} {DSeed : Type*}
    [Fintype DSeed] [Nonempty DSeed]
    (f : (Fin n → Bool) → Rat)
    (D : DSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased q D) :
    highTailFarPairCorrelation f cutoff q D allFalseMask =
      finiteAverage (fun seed : DSeed =>
        (ratHighDegreeFourierTail f cutoff (D seed)) ^ 2) -
        ∑ support ∈ highDegreeSupports n cutoff,
          (coefficient f support) ^ 2 := by
  have hsplit := unmaskedHighTail_secondMoment_eq_diagonal_add_far
    (cutoff := cutoff) (q := q) f D hD
  linarith

/-- The signed far sum of the structured base source against the all-false
mask has absolute value at most four. -/
theorem abs_structured_allFalse_highTailFarPairCorrelation_le_four
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1) :
    |highTailFarPairCorrelation f (2 * m) (structuredIndependence m)
        (structuredUnbiasedPrimitive n m hn).generate allFalseMask| ≤ 4 := by
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let energy := finiteAverage
    (fun seed : Fin (structuredIndependence m * n) → Bool =>
      (ratHighDegreeFourierTail f (2 * m) (D seed)) ^ 2)
  let diagonal := ∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
    (coefficient f support) ^ 2
  have hfar :
      highTailFarPairCorrelation f (2 * m) (structuredIndependence m)
          D allFalseMask = energy - diagonal := by
    exact allFalse_highTailFarPairCorrelation_eq_sub_diagonal
      f D (structuredUnbiasedPrimitive_patternUnbiased n m hn)
  have henergy0 : 0 ≤ energy := by
    unfold energy finiteAverage
    positivity
  have henergy4 : energy ≤ 4 := by
    exact structured_unmaskedHighTail_secondMoment_le_four
      n m hn f hbounded
  have hdiagonal0 : 0 ≤ diagonal := by
    unfold diagonal
    positivity
  have hdiagonal1 : diagonal ≤ 1 := by
    unfold diagonal
    exact (bessel f (highDegreeSupports (2 ^ n) (2 * m))).trans
      (finiteAverage_sq_le_one_of_abs_le_one f hbounded)
  rw [hfar, abs_le]
  constructor <;> linarith

/-- In the full-field mask, every structured dual far pair has the same
survival factor `p^(4m+1)`.  The remaining signed sum is precisely the
all-false far correlation of the structured base code. -/
theorem structuredDualFarPairCorrelation_full_eq_pow_mul_allFalse
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    structuredDualFarPairCorrelation n m n (2 * m) hn (by omega) f =
      (1 / (2 : Rat) ^ n) ^ structuredIndependence m *
        highTailFarPairCorrelation f (2 * m) (structuredIndependence m)
          (structuredUnbiasedPrimitive n m hn).generate allFalseMask := by
  classical
  unfold structuredDualFarPairCorrelation highTailFarPairCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left hleft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right hright
  by_cases hfar : left ≠ right ∧
      structuredIndependence m < (left ∆ right).card
  · by_cases hdual : IsStructuredDualSupport n
        (structuredIndependence m) hn (left ∆ right)
    · have hcard : structuredIndependence m ≤ (left ∪ right).card := by
        calc
          structuredIndependence m ≤ (left ∆ right).card :=
            Nat.le_of_lt hfar.2
          _ ≤ (left ∪ right).card :=
            Finset.card_le_card Finset.symmDiff_subset_union
      have hmask :=
        structuredDyadicPrimitive_pairUnionFullMaskSurvival_exact
          n m hn left right hcard
      have hpair :=
        structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq
          n m hn (allFalseMask (n := 2 ^ n)) left right
      rw [if_pos ⟨hfar.1, hfar.2, hdual⟩, if_pos hfar, hmask, hpair]
      simp [hdual, allFalseMask, maskAllZeroIndicator, finiteAverage]
      ring
    · have hcombined : ¬ (left ≠ right ∧
          structuredIndependence m < (left ∆ right).card ∧
          IsStructuredDualSupport n (structuredIndependence m) hn
            (left ∆ right)) := by
        intro h
        exact hdual h.2.2
      have hpair :=
        structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq
          n m hn (allFalseMask (n := 2 ^ n)) left right
      rw [if_neg hcombined, if_pos hfar, hpair]
      simp [hdual]
  · have hcombined : ¬ (left ≠ right ∧
        structuredIndependence m < (left ∆ right).card ∧
        IsStructuredDualSupport n (structuredIndependence m) hn
          (left ∆ right)) := by
      intro h
      exact hfar ⟨h.1, h.2.1⟩
    rw [if_neg hcombined, if_neg hfar]
    simp

/-- The full-field structured dual far correlation is uniformly bounded by
`4 p^(4m+1)`, independently of the ambient truth-table size. -/
theorem abs_structuredDualFarPairCorrelation_full_le_four_mul_pow
    (n m : Nat) (hn : 0 < n)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1) :
    |structuredDualFarPairCorrelation n m n (2 * m) hn (by omega) f| ≤
      4 * (1 / (2 : Rat) ^ n) ^ structuredIndependence m := by
  rw [structuredDualFarPairCorrelation_full_eq_pow_mul_allFalse,
    abs_mul]
  have hp0 :
      0 ≤ (1 / (2 : Rat) ^ n) ^ structuredIndependence m := by
    positivity
  rw [abs_of_nonneg hp0]
  calc
    (1 / (2 : Rat) ^ n) ^ structuredIndependence m *
          |highTailFarPairCorrelation f (2 * m) (structuredIndependence m)
            (structuredUnbiasedPrimitive n m hn).generate allFalseMask| ≤
        (1 / (2 : Rat) ^ n) ^ structuredIndependence m * 4 :=
      mul_le_mul_of_nonneg_left
        (abs_structured_allFalse_highTailFarPairCorrelation_le_four
          n m hn f hbounded) hp0
    _ = 4 * (1 / (2 : Rat) ^ n) ^ structuredIndependence m := by ring

/-- For positive `m,n`, the full-field correlation estimate fits exactly
inside the off-diagonal budget left after the `p^(2m+1)` diagonal term. -/
theorem four_mul_fullFieldPow_le_dualFarBudget
    (n m : Nat) (hn : 0 < n) (hm : 0 < m) :
    4 * (1 / (2 : Rat) ^ n) ^ structuredIndependence m ≤
      (1 - 1 / (2 : Rat) ^ n) *
        (1 / (2 : Rat) ^ n) ^ (2 * m) := by
  let p : Rat := 1 / (2 : Rat) ^ n
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hpHalf : p ≤ (1 / 2 : Rat) := by
    dsimp [p]
    apply one_div_le_one_div_of_le (by norm_num : (0 : Rat) < 2)
    exact_mod_cast (show 2 ≤ 2 ^ n by
      calc
        2 = 2 ^ (1 : Nat) := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have hp1 : p ≤ 1 := hpHalf.trans (by norm_num)
  have htailCube : p ^ (2 * m + 1) ≤ (1 / 8 : Rat) := by
    calc
      p ^ (2 * m + 1) ≤ p ^ 3 :=
        pow_le_pow_of_le_one hp0 hp1 (by omega)
      _ ≤ (1 / 2 : Rat) ^ 3 := pow_le_pow_left₀ hp0 hpHalf 3
      _ = (1 / 8 : Rat) := by norm_num
  have htailBudget : 4 * p ^ (2 * m + 1) ≤ 1 - p := by
    nlinarith
  change 4 * p ^ structuredIndependence m ≤
    (1 - p) * p ^ (2 * m)
  calc
    4 * p ^ structuredIndependence m =
        p ^ (2 * m) * (4 * p ^ (2 * m + 1)) := by
      unfold structuredIndependence
      rw [show 4 * m + 1 = 2 * m + (2 * m + 1) by omega, pow_add]
      ring
    _ ≤ p ^ (2 * m) * (1 - p) :=
      mul_le_mul_of_nonneg_left htailBudget (pow_nonneg hp0 _)
    _ = (1 - p) * p ^ (2 * m) := by ring

/-- Absolute full-field dual correlation fits the exact selector-pair budget. -/
theorem abs_structuredDualFarPairCorrelation_full_le_dualFarBudget
    (n m : Nat) (hn : 0 < n) (hm : 0 < m)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1) :
    |structuredDualFarPairCorrelation n m n (2 * m) hn (by omega) f| ≤
      (1 - 1 / (2 : Rat) ^ n) *
        (1 / (2 : Rat) ^ n) ^ (2 * m) := by
  exact (abs_structuredDualFarPairCorrelation_full_le_four_mul_pow
    n m hn f hbounded).trans
      (four_mul_fullFieldPow_le_dualFarBudget n m hn hm)

/-- The signed form required by `DualFarBound`; it follows from the stronger
absolute estimate. -/
theorem structuredDualFarPairCorrelation_full_le_dualFarBudget
    (n m : Nat) (hn : 0 < n) (hm : 0 < m)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1) :
    structuredDualFarPairCorrelation n m n (2 * m) hn (by omega) f ≤
      (1 - 1 / (2 : Rat) ^ n) *
        (1 / (2 : Rat) ^ n) ^ (2 * m) := by
  exact (le_abs_self _).trans
    (abs_structuredDualFarPairCorrelation_full_le_dualFarBudget
      n m hn hm f hbounded)

/-! ## Size-free full-field second and first moments -/

/-- For positive `m,n`, the structured full-field restriction has high-tail
second moment at most `p^(2m)`. -/
theorem structured_fullField_highTail_restriction_secondMoment_le_pow
    (n m : Nat) (hn : 0 < n) (hm : 0 < m)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) ↦
      (finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
        ratHighDegreeFourierTail f (2 * m)
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m n hn (by omega)).generate seed.2)
            uniform))) ^ 2) ≤
      (1 / (2 : Rat) ^ n) ^ (2 * m) := by
  have hsecond :=
    structured_highTail_restriction_secondMoment_le_pow_succ_add_abs_far
      n m n hn (by omega) f hbounded
  rw [structured_highTailFarPairCorrelation_eq_dual] at hsecond
  calc
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) ↦
      (finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
        ratHighDegreeFourierTail f (2 * m)
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m n hn (by omega)).generate seed.2)
            uniform))) ^ 2) ≤
      (1 / (2 : Rat) ^ n) ^ (2 * m + 1) +
        |structuredDualFarPairCorrelation n m n (2 * m)
          hn (by omega) f| := hsecond
    _ ≤ (1 / (2 : Rat) ^ n) ^ (2 * m + 1) +
        (1 - 1 / (2 : Rat) ^ n) *
          (1 / (2 : Rat) ^ n) ^ (2 * m) :=
      add_le_add_left
        (abs_structuredDualFarPairCorrelation_full_le_dualFarBudget
          n m hn hm f hbounded) _
    _ = (1 / (2 : Rat) ^ n) ^ (2 * m) := by
      rw [pow_succ]
      ring

/-- Cauchy--Schwarz turns the full-field second-moment estimate into the
size-free absolute first moment `p^m`. -/
theorem structured_fullField_highTail_restriction_absMoment_le_pow
    (n m : Nat) (hn : 0 < n) (hm : 0 < m)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) ↦
      |finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
        ratHighDegreeFourierTail f (2 * m)
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m n hn (by omega)).generate seed.2)
            uniform))|) ≤
      (1 / (2 : Rat) ^ n) ^ m := by
  let tailAverage := fun seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n) ↦
    finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
      ratHighDegreeFourierTail f (2 * m)
        (maskedInput
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m n hn (by omega)).generate seed.2)
          uniform))
  have hsecond :=
    structured_fullField_highTail_restriction_secondMoment_le_pow
      n m hn hm f hbounded
  change finiteAverage (fun seed => (tailAverage seed) ^ 2) ≤
    (1 / (2 : Rat) ^ n) ^ (2 * m) at hsecond
  have habsSquare :
      (finiteAverage (fun seed => |tailAverage seed|)) ^ 2 ≤
        (1 / (2 : Rat) ^ n) ^ (2 * m) :=
    (finiteAverage_abs_sq_le_average_sq tailAverage).trans hsecond
  have hp0 : 0 ≤ (1 / (2 : Rat) ^ n) ^ m := by positivity
  have havg0 :
      0 ≤ finiteAverage (fun seed => |tailAverage seed|) := by
    unfold finiteAverage
    positivity
  apply FiniteBooleanVertexSumRestrictionBound.le_of_sq_le_sq_of_nonneg
    havg0 hp0
  simpa [show 2 * m = m + m by omega, pow_add, pow_two] using habsSquare

/-- The complete one-round full-field restriction changes the expectation of
any bounded function by at most `p^m`.  Low degrees cancel exactly; the
preceding absolute high-tail moment controls the remainder. -/
theorem structured_fullField_oneRoundError_le_pow
    (n m : Nat) (hn : 0 < n) (hm : 0 < m)
    (f : (Fin (2 ^ n) → Bool) → Rat)
    (hbounded : ∀ input, |f input| ≤ 1) :
    |finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) ↦
      finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
        f (maskedInput
          ((structuredUnbiasedPrimitive n m hn).generate seed.1)
          ((structuredDyadicPrimitive n m n hn (by omega)).generate seed.2)
          uniform))) - finiteAverage f| ≤
      (1 / (2 : Rat) ^ n) ^ m := by
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m n hn (by omega)).generate
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
            FiniteBitTape (structuredIndependence m * n) ↦
        finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
          f (maskedInput (D seed.1) (mask seed.2) uniform))) -
          finiteAverage f =
        finiteAverage (fun seed :
          FiniteBitTape (structuredIndependence m * n) ×
            FiniteBitTape (structuredIndependence m * n) ↦
          finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
            ratHighDegreeFourierTail f (2 * m)
              (maskedInput (D seed.1) (mask seed.2) uniform))) := by
    rw [hexact]
    ring
  let tailAverage := fun seed :
      FiniteBitTape (structuredIndependence m * n) ×
        FiniteBitTape (structuredIndependence m * n) ↦
    finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
      ratHighDegreeFourierTail f (2 * m)
        (maskedInput (D seed.1) (mask seed.2) uniform))
  have habs := structured_fullField_highTail_restriction_absMoment_le_pow
    n m hn hm f hbounded
  change finiteAverage (fun seed => |tailAverage seed|) ≤
    (1 / (2 : Rat) ^ n) ^ m at habs
  change
    |finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) ↦
      finiteAverage (fun uniform : Fin (2 ^ n) → Bool ↦
        f (maskedInput (D seed.1) (mask seed.2) uniform))) -
      finiteAverage f| ≤ (1 / (2 : Rat) ^ n) ^ m
  rw [hgap]
  calc
    |finiteAverage tailAverage| ≤
        finiteAverage (fun seed => |tailAverage seed|) :=
      abs_finiteAverage_le_finiteAverage_abs tailAverage
    _ ≤ (1 / (2 : Rat) ^ n) ^ m := habs

end DPTWStructuredFullFieldCorrelation

end
end OneTapeMagnification
end Frontier
end Pnp4
