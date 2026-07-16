import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredUnbiasedDualCode
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# What one extra independence order does and does not prove

This module isolates the proposed replacement `4 * m + 2` for the
structured base source.  The extra order diagonalizes the first strict-high
homogeneous layer, of degree `2 * m + 1`.  It does not diagonalize the whole
strict `> 2 * m` tail: a concrete degree-four pair at `m = 1` still differs
by a dual word for the degree-`< 6` evaluation code.

This is lower-layer infrastructure.  It does not reduce either mainline
source obligation.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanFourierEnergy
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanBoundedIndependenceFarTail
open DPTWFiniteFieldKWiseSeed
open GaloisBilinearTensorBridge
open DPTWStructuredFieldCoordinatePrimitive
open DPTWStructuredUnbiasedDualCode

namespace DPTWStructuredIndependencePlusOneNoGo

local instance plusOneDualSupportDecidable
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    Decidable (IsStructuredDualSupport n k hn support) :=
  Classical.propDecidable _

/-- The proposed one-order strengthening of the structured independence. -/
def structuredIndependencePlusOne (m : Nat) : Nat := 4 * m + 2

/-- The dyadically biased structured source with degree bound `4m+2`. -/
def structuredDyadicSourcePlusOne
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n) :
    (Fin (structuredIndependencePlusOne m * n) -> Bool) ->
      Fin (2 ^ n) -> Bool :=
  structuredPolynomialSubsetSource n (structuredIndependencePlusOne m)
    (Nat.ne_of_gt hn)
    (zeroPrefixFalseSet n tailBits (Nat.ne_of_gt hn) htail)

/-- Its exact false-biased product law through all `4m+2` queries. -/
theorem structuredDyadicSourcePlusOne_patternFalseBiased
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n) :
    IsKWisePatternFalseBiased (structuredIndependencePlusOne m)
      (1 / (2 : Rat) ^ tailBits)
      (structuredDyadicSourcePlusOne n m tailBits hn htail) := by
  unfold structuredDyadicSourcePlusOne
  have hlaw := structuredPolynomialSubsetSource_isKWisePatternFalseBiased
    n (structuredIndependencePlusOne m) (Nat.ne_of_gt hn)
    (zeroPrefixFalseSet n tailBits (Nat.ne_of_gt hn) htail)
  rw [zeroPrefixFalseSet_exactMass n tailBits (Nat.ne_of_gt hn) htail]
    at hlaw
  exact hlaw

/-- The Boolean seed corresponding to the zero bounded-degree polynomial. -/
noncomputable def structuredZeroPolynomialSeedPlusOne
    (n m : Nat) (hn : 0 < n) :
    Fin (structuredIndependencePlusOne m * n) -> Bool :=
  (structuredPolynomialBitSeedEquiv
    (structuredIndependencePlusOne m) n (Nat.ne_of_gt hn)).symm 0

/-- The zero-polynomial seed makes every dyadic source coordinate false. -/
@[simp]
theorem structuredDyadicSourcePlusOne_zeroPolynomialSeed
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (index : Fin (2 ^ n)) :
    structuredDyadicSourcePlusOne n m tailBits hn htail
        (structuredZeroPolynomialSeedPlusOne n m hn) index = false := by
  unfold structuredDyadicSourcePlusOne structuredZeroPolynomialSeedPlusOne
    structuredPolynomialSubsetSource polynomialSubsetSource
  rw [Equiv.apply_symm_apply]
  rw [fieldSubsetCoin_eq_false_iff,
    mem_zeroPrefixFalseSet]
  intro prefixIndex
  simp

/-- Hence no union support is annihilated identically by the stronger mask:
its all-zero survival probability is strictly positive. -/
theorem structuredDyadicSourcePlusOne_maskSurvival_pos
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (support : Finset (Fin (2 ^ n))) :
    0 < finiteAverage
      (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
        maskAllZeroIndicator support
          (structuredDyadicSourcePlusOne n m tailBits hn htail seed)) := by
  classical
  let zeroSeed := structuredZeroPolynomialSeedPlusOne n m hn
  have hone :
      maskAllZeroIndicator support
          (structuredDyadicSourcePlusOne n m tailBits hn htail zeroSeed) = 1 := by
    unfold maskAllZeroIndicator
    rw [if_pos]
    intro index hindex
    exact structuredDyadicSourcePlusOne_zeroPolynomialSeed
      n m tailBits hn htail index
  have hnonnegative :
      ∀ seed ∈
          (Finset.univ :
            Finset (Fin (structuredIndependencePlusOne m * n) -> Bool)),
        (0 : Rat) <=
          maskAllZeroIndicator support
            (structuredDyadicSourcePlusOne n m tailBits hn htail seed) := by
    intro seed _
    unfold maskAllZeroIndicator
    split <;> norm_num
  have hsingle :
      maskAllZeroIndicator support
          (structuredDyadicSourcePlusOne n m tailBits hn htail zeroSeed) <=
        ∑ seed : Fin (structuredIndependencePlusOne m * n) -> Bool,
          maskAllZeroIndicator support
            (structuredDyadicSourcePlusOne n m tailBits hn htail seed) :=
    Finset.single_le_sum hnonnegative (Finset.mem_univ zeroSeed)
  have hsumPositive :
      (0 : Rat) <
        ∑ seed : Fin (structuredIndependencePlusOne m * n) -> Bool,
          maskAllZeroIndicator support
            (structuredDyadicSourcePlusOne n m tailBits hn htail seed) :=
    lt_of_lt_of_le (by rw [hone]; norm_num) hsingle
  unfold finiteAverage
  exact div_pos hsumPositive (by positivity)

/-- The unbiased structured evaluation source with degree bound `4m+2`.
This is the distributional core of the proposed stronger primitive; no
circuit claim is needed for the Gram calculation below. -/
def structuredUnbiasedSourcePlusOne
    (n m : Nat) (hn : 0 < n) :
    (Fin (structuredIndependencePlusOne m * n) -> Bool) ->
      Fin (2 ^ n) -> Bool :=
  structuredDyadicSourcePlusOne n m 1 hn (by omega)

/-- The stronger source still has the exact product law through its full
`4m+2` query budget. -/
theorem structuredUnbiasedSourcePlusOne_patternUnbiased
    (n m : Nat) (hn : 0 < n) :
    IsKWisePatternUnbiased (structuredIndependencePlusOne m)
      (structuredUnbiasedSourcePlusOne n m hn) := by
  intro support hcard pattern
  have hbiased :=
    structuredPolynomialSubsetSource_isKWisePatternFalseBiased
      n (structuredIndependencePlusOne m) (Nat.ne_of_gt hn)
      (zeroPrefixFalseSet n 1 (Nat.ne_of_gt hn) (by omega))
      support hcard pattern
  rw [zeroPrefixFalseSet_exactMass n 1 (Nat.ne_of_gt hn) (by omega)]
    at hbiased
  change finiteAverage (fun seed =>
      localPatternIndicator support pattern
        (structuredPolynomialSubsetSource n
          (structuredIndependencePlusOne m) (Nat.ne_of_gt hn)
          (zeroPrefixFalseSet n 1 (Nat.ne_of_gt hn) (by omega)) seed)) = _
  rw [hbiased]
  norm_num
  simpa [one_div] using
    (DPTWFiniteFieldKWiseSeed.localPatternProductMass_half pattern)

/-- At every degree, the exact Walsh law is still the dual-code indicator. -/
theorem structuredUnbiasedSourcePlusOne_characterAverage_eq_dualIndicator
    (n m : Nat) (hn : 0 < n)
    (support : Finset (Fin (2 ^ n))) :
    finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
          character support (structuredUnbiasedSourcePlusOne n m hn seed)) =
      if IsStructuredDualSupport n (structuredIndependencePlusOne m) hn support
        then 1 else 0 := by
  calc
    finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
          character support (structuredUnbiasedSourcePlusOne n m hn seed)) =
      finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
          character support
            (structuredEvaluationBit n (structuredIndependencePlusOne m) hn
              (structuredPolynomialBitSeedEquiv
                (structuredIndependencePlusOne m) n (Nat.ne_of_gt hn)
                seed))) := by
          apply finiteAverage_congr
          intro seed
          congr 1
          funext index
          exact structuredPolynomialSubsetSource_one_eq_evaluationBit
            n (structuredIndependencePlusOne m) hn seed index
    _ = finiteAverage
        (fun polynomial : Polynomial.degreeLT
            (GaloisField 2 n) (structuredIndependencePlusOne m) =>
          character support
            (structuredEvaluationBit n (structuredIndependencePlusOne m) hn
              polynomial)) := by
          simpa using
            (DPTWFiniteFieldKWiseSeed.finiteAverage_comp_equiv
              (structuredPolynomialBitSeedEquiv
                (structuredIndependencePlusOne m) n (Nat.ne_of_gt hn))
              (fun polynomial : Polynomial.degreeLT
                  (GaloisField 2 n) (structuredIndependencePlusOne m) =>
                character support
                  (structuredEvaluationBit n
                    (structuredIndependencePlusOne m) hn polynomial)))
    _ = _ := finiteAverage_structuredSupportAddChar
      n (structuredIndependencePlusOne m) hn support

/-- Exact pair Gram entry for the stronger source. -/
theorem structuredUnbiasedSourcePlusOne_characterPairAverage_eq_dualIndicator
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n))) :
    finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
          character left (structuredUnbiasedSourcePlusOne n m hn seed) *
            character right (structuredUnbiasedSourcePlusOne n m hn seed)) =
      if IsStructuredDualSupport n (structuredIndependencePlusOne m) hn
          (left ∆ right)
        then 1 else 0 := by
  calc
    finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
          character left (structuredUnbiasedSourcePlusOne n m hn seed) *
            character right (structuredUnbiasedSourcePlusOne n m hn seed)) =
      finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
          character (left ∆ right)
            (structuredUnbiasedSourcePlusOne n m hn seed)) := by
          apply finiteAverage_congr
          intro seed
          exact character_mul_character_eq_symmDiff left right _
    _ = _ :=
      structuredUnbiasedSourcePlusOne_characterAverage_eq_dualIndicator
        n m hn (left ∆ right)

/-- The corresponding restricted-character pair moment keeps precisely the
same dual indicator and the mask-survival factor. -/
theorem structuredUnbiasedSourcePlusOne_restrictedCharacterPairMoment_eq
    (n m : Nat) (hn : 0 < n)
    {TSeed : Type*} [Fintype TSeed] [Nonempty TSeed]
    (mask : TSeed -> Fin (2 ^ n) -> Bool)
    (left right : Finset (Fin (2 ^ n))) :
    finiteAverage
        (fun seed :
            (Fin (structuredIndependencePlusOne m * n) -> Bool) × TSeed =>
          restrictedCharacterAverage left
              (structuredUnbiasedSourcePlusOne n m hn seed.1) (mask seed.2) *
            restrictedCharacterAverage right
              (structuredUnbiasedSourcePlusOne n m hn seed.1)
              (mask seed.2)) =
      (if IsStructuredDualSupport n (structuredIndependencePlusOne m) hn
          (left ∆ right) then 1 else 0) *
        finiteAverage (fun seed : TSeed =>
          maskAllZeroIndicator (left ∪ right) (mask seed)) := by
  rw [restrictedCharacterAverage_pairMoment_eq]
  rw [structuredUnbiasedSourcePlusOne_characterAverage_eq_dualIndicator]

/-- No nonempty dual word fits inside the stronger independence budget. -/
theorem not_isStructuredDualSupport_plusOne_of_nonempty_card_le
    (n m : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (hcard : support.card <= structuredIndependencePlusOne m)
    (hnonempty : support.Nonempty) :
    ¬ IsStructuredDualSupport n (structuredIndependencePlusOne m) hn
      support := by
  intro hdual
  have hzero :
      finiteAverage
          (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
            character support (structuredUnbiasedSourcePlusOne n m hn seed)) =
        0 :=
    character_average_eq_zero_of_patternUnbiased
      (structuredUnbiasedSourcePlusOne n m hn)
      (structuredUnbiasedSourcePlusOne_patternUnbiased n m hn)
      support hcard hnonempty
  have hone :
      finiteAverage
          (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
            character support (structuredUnbiasedSourcePlusOne n m hn seed)) =
        1 := by
    rw [structuredUnbiasedSourcePlusOne_characterAverage_eq_dualIndicator,
      if_pos hdual]
  linarith

/-- Every nonempty dual word left by the stronger source starts strictly
above `4m+2`, hence has at least `4m+3` coordinates. -/
theorem structuredIndependencePlusOne_lt_card_of_nonempty_dual
    (n m : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (hnonempty : support.Nonempty)
    (hdual : IsStructuredDualSupport n (structuredIndependencePlusOne m) hn
      support) :
    structuredIndependencePlusOne m < support.card := by
  by_contra hnot
  exact (not_isStructuredDualSupport_plusOne_of_nonempty_card_le
    n m hn support (Nat.le_of_not_gt hnot) hnonempty) hdual

/-- Exact classification of the possible off-diagonal aliases: their
symmetric differences have size at least `4m+3`. -/
theorem structuredIndependencePlusOne_lt_symmDiff_card_of_distinct_dual
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n))) (hne : left ≠ right)
    (hdual : IsStructuredDualSupport n (structuredIndependencePlusOne m) hn
      (left ∆ right)) :
    structuredIndependencePlusOne m < (left ∆ right).card :=
  structuredIndependencePlusOne_lt_card_of_nonempty_dual
    n m hn (left ∆ right) (Finset.symmDiff_nonempty.mpr hne) hdual

/-- Consequently every surviving distinct pair also has union size at least
`4m+3`; this is termwise mask damping, not an aggregate row bound. -/
theorem structuredIndependencePlusOne_lt_union_card_of_distinct_dual
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n))) (hne : left ≠ right)
    (hdual : IsStructuredDualSupport n (structuredIndependencePlusOne m) hn
      (left ∆ right)) :
    structuredIndependencePlusOne m < (left ∪ right).card :=
  (structuredIndependencePlusOne_lt_symmDiff_card_of_distinct_dual
    n m hn left right hne hdual).trans_le
      (Finset.card_le_card Finset.symmDiff_subset_union)

/-- Item (a): the complete degree-`2m+1` Gram block is diagonal. -/
theorem structuredUnbiasedSourcePlusOne_degree_two_mul_add_one_gram_diagonal
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n)))
    (hleft : left.card = 2 * m + 1)
    (hright : right.card = 2 * m + 1) :
    finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
          character left (structuredUnbiasedSourcePlusOne n m hn seed) *
            character right (structuredUnbiasedSourcePlusOne n m hn seed)) =
      if left = right then 1 else 0 := by
  by_cases heq : left = right
  · subst right
    rw [if_pos rfl]
    simp [character_square, finiteAverage]
  · rw [if_neg heq]
    have hcard : (left ∆ right).card <= structuredIndependencePlusOne m := by
      calc
        (left ∆ right).card <= left.card + right.card :=
          card_symmDiff_le_add left right
        _ = structuredIndependencePlusOne m := by
          rw [hleft, hright]
          simp [structuredIndependencePlusOne]
          omega
    calc
      finiteAverage
          (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
            character left (structuredUnbiasedSourcePlusOne n m hn seed) *
              character right
                (structuredUnbiasedSourcePlusOne n m hn seed)) =
        finiteAverage
          (fun seed : Fin (structuredIndependencePlusOne m * n) -> Bool =>
            character (left ∆ right)
              (structuredUnbiasedSourcePlusOne n m hn seed)) := by
            apply finiteAverage_congr
            intro seed
            exact character_mul_character_eq_symmDiff left right _
      _ = 0 := character_pair_average_eq_zero_of_patternUnbiased
        (structuredUnbiasedSourcePlusOne n m hn)
        (structuredUnbiasedSourcePlusOne_patternUnbiased n m hn)
        left right heq hcard

abbrev EightCoordinate := Fin (2 ^ 3)
abbrev EightField := GaloisField 2 3

/-! ## Item (b): an explicit dual alias above the diagonalized layer -/

/-- `GF(8)ˣ` has an element of order seven. -/
theorem exists_seventhRootUnit :
    ∃ root : EightFieldˣ, orderOf root = 7 := by
  have hfieldCard : Fintype.card EightField = 8 := by
    simpa using binaryGaloisField_card 3 (by omega)
  have hdiv : 7 ∣ Fintype.card EightFieldˣ := by
    rw [Fintype.card_units, hfieldCard]
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_prime_orderOf_dvd_card 7 hdiv

noncomputable def seventhRootUnit : EightFieldˣ :=
  Classical.choose exists_seventhRootUnit

theorem seventhRootUnit_order : orderOf seventhRootUnit = 7 :=
  Classical.choose_spec exists_seventhRootUnit

theorem seventhRoot_isPrimitiveRoot :
    IsPrimitiveRoot (seventhRootUnit : EightField) 7 := by
  rw [IsPrimitiveRoot.coe_units_iff]
  simpa [seventhRootUnit_order] using
    (IsPrimitiveRoot.orderOf seventhRootUnit)

/-- Encode a field element by the coordinate decoded to it by the same
classically chosen basis as the structured source. -/
noncomputable def eightFieldIndex (value : EightField) : EightCoordinate :=
  StreamingMagnification.FixedBitstringCodec.rank
    (gfTwoBoolCoordinates 3 (by omega) value)

theorem eightFieldIndex_injective : Function.Injective eightFieldIndex := by
  intro left right hequal
  apply (gfTwoBoolCoordinates 3 (by omega)).injective
  exact StreamingMagnification.FixedBitstringCodec.rank_injective hequal

@[simp]
theorem structuredTruthTableNode_eightFieldIndex (value : EightField) :
    structuredTruthTableNode 3 (by omega) (eightFieldIndex value) = value := by
  unfold structuredTruthTableNode eightFieldIndex
  rw [← StreamingMagnification.FixedBitstringCodec.unrank_eq_lexInput,
    StreamingMagnification.FixedBitstringCodec.unrank_rank,
    Equiv.symm_apply_apply]

/-- All seven seventh roots of unity, transported to truth-table
coordinates. -/
noncomputable def seventhRootIndexSet : Finset EightCoordinate :=
  (Finset.range 7).image (fun exponent =>
    eightFieldIndex ((seventhRootUnit : EightField) ^ exponent))

theorem seventhRootIndexSet_card : seventhRootIndexSet.card = 7 := by
  classical
  unfold seventhRootIndexSet
  rw [Finset.card_image_of_injOn]
  · simp
  · intro left hleft right hright hequal
    apply seventhRoot_isPrimitiveRoot.injOn_pow hleft hright
    exact eightFieldIndex_injective hequal

theorem eightFieldIndex_zero_not_mem_seventhRootIndexSet :
    eightFieldIndex (0 : EightField) ∉ seventhRootIndexSet := by
  classical
  intro hmem
  rw [seventhRootIndexSet, Finset.mem_image] at hmem
  obtain ⟨exponent, _, hequal⟩ := hmem
  have hfieldEqual :
      (seventhRootUnit : EightField) ^ exponent = 0 :=
    eightFieldIndex_injective hequal
  exact (pow_ne_zero exponent seventhRootUnit.ne_zero) hfieldEqual

/-- Zero together with all seven roots is an eight-point dual word. -/
noncomputable def plusOneDualWord : Finset EightCoordinate :=
  insert (eightFieldIndex (0 : EightField)) seventhRootIndexSet

theorem plusOneDualWord_card : plusOneDualWord.card = 8 := by
  classical
  rw [plusOneDualWord,
    Finset.card_insert_of_notMem
      eightFieldIndex_zero_not_mem_seventhRootIndexSet,
    seventhRootIndexSet_card]

theorem sum_seventhRootIndexSet_node_pow (exponent : Nat) :
    (∑ index ∈ seventhRootIndexSet,
        structuredTruthTableNode 3 (by omega) index ^ exponent) =
      ∑ power ∈ Finset.range 7,
        ((seventhRootUnit : EightField) ^ power) ^ exponent := by
  classical
  have hinjective : Set.InjOn
      (fun power : Nat =>
        eightFieldIndex ((seventhRootUnit : EightField) ^ power))
      (Finset.range 7) := by
    intro left hleft right hright hequal
    apply seventhRoot_isPrimitiveRoot.injOn_pow hleft hright
    exact eightFieldIndex_injective hequal
  unfold seventhRootIndexSet
  rw [Finset.sum_image hinjective]
  apply Finset.sum_congr rfl
  intro power _
  rw [structuredTruthTableNode_eightFieldIndex]

/-- Every power sum needed by degree `< 6` vanishes on the eight-point word. -/
theorem plusOneDualWord_powerSum_eq_zero (exponent : Fin 6) :
    structuredSupportPowerSum 3 (by omega) plusOneDualWord exponent.val = 0 := by
  classical
  unfold structuredSupportPowerSum plusOneDualWord
  rw [Finset.sum_insert eightFieldIndex_zero_not_mem_seventhRootIndexSet,
    structuredTruthTableNode_eightFieldIndex,
    sum_seventhRootIndexSet_node_pow]
  by_cases hzero : exponent.val = 0
  · simp [hzero]
    have hchar : (2 : EightField) = 0 :=
      CharP.cast_eq_zero EightField 2
    calc
      (1 : EightField) + 7 = 8 := by norm_num
      _ = 4 * 2 := by norm_num
      _ = 0 := by rw [hchar, mul_zero]
  · have hcases : exponent.val = 1 ∨ exponent.val = 2 ∨
        exponent.val = 3 ∨ exponent.val = 4 ∨ exponent.val = 5 := by
      omega
    have hcoprime : exponent.val.Coprime 7 := by
      rcases hcases with h | h | h | h | h
      · simp [h]
      · simpa [h] using (by decide : Nat.Coprime 2 7)
      · simpa [h] using (by decide : Nat.Coprime 3 7)
      · simpa [h] using (by decide : Nat.Coprime 4 7)
      · simpa [h] using (by decide : Nat.Coprime 5 7)
    have hprimitive :
        IsPrimitiveRoot
          ((seventhRootUnit : EightField) ^ exponent.val) 7 :=
      seventhRoot_isPrimitiveRoot.pow_of_coprime exponent.val hcoprime
    rw [zero_pow hzero, zero_add]
    convert hprimitive.geom_sum_eq_zero (by omega) using 1
    apply Finset.sum_congr rfl
    intro power _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem plusOneDualWord_isStructuredDualSupport :
    IsStructuredDualSupport 3 (structuredIndependencePlusOne 1) (by omega)
      plusOneDualWord := by
  rw [isStructuredDualSupport_iff_powerSums_eq_zero]
  simpa [structuredIndependencePlusOne] using plusOneDualWord_powerSum_eq_zero

/-- One four-point half of the dual word. -/
noncomputable def plusOneLeft : Finset EightCoordinate :=
  Classical.choose
    (Finset.exists_subset_card_eq
      (s := plusOneDualWord) (n := 4)
        (by rw [plusOneDualWord_card]; omega))

theorem plusOneLeft_subset : plusOneLeft ⊆ plusOneDualWord :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := plusOneDualWord) (n := 4)
        (by rw [plusOneDualWord_card]; omega))).1

theorem plusOneLeft_card : plusOneLeft.card = 4 :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := plusOneDualWord) (n := 4)
        (by rw [plusOneDualWord_card]; omega))).2

/-- The complementary four-point half. -/
noncomputable def plusOneRight : Finset EightCoordinate :=
  plusOneDualWord \ plusOneLeft

theorem plusOneRight_card : plusOneRight.card = 4 := by
  rw [plusOneRight, Finset.card_sdiff plusOneLeft_subset,
    plusOneDualWord_card, plusOneLeft_card]

theorem plusOneLeft_disjoint_plusOneRight :
    Disjoint plusOneLeft plusOneRight := by
  exact Finset.disjoint_sdiff

theorem plusOneLeft_symmDiff_plusOneRight :
    plusOneLeft ∆ plusOneRight = plusOneDualWord := by
  rw [Finset.symmDiff_eq_union plusOneLeft_disjoint_plusOneRight]
  exact Finset.union_sdiff_of_subset plusOneLeft_subset

theorem plusOneLeft_union_plusOneRight :
    plusOneLeft ∪ plusOneRight = plusOneDualWord :=
  Finset.union_sdiff_of_subset plusOneLeft_subset

theorem plusOneLeft_ne_plusOneRight : plusOneLeft ≠ plusOneRight := by
  intro hequal
  have hword := plusOneLeft_symmDiff_plusOneRight
  simp [hequal] at hword
  have hcard := congrArg Finset.card hword
  rw [plusOneDualWord_card] at hcard
  simp at hcard

/-- Item (b), concretely: at `m=1`, a distinct degree-four pair survives
with Gram entry one even though the degree-three block is diagonal. -/
theorem structuredUnbiasedSourcePlusOne_degreeFour_alias_eq_one :
    finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne 1 * 3) -> Bool =>
          character plusOneLeft
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed) *
            character plusOneRight
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed)) =
      1 := by
  rw [structuredUnbiasedSourcePlusOne_characterPairAverage_eq_dualIndicator]
  rw [plusOneLeft_symmDiff_plusOneRight]
  simp [plusOneDualWord_isStructuredDualSupport]

/-- The same alias survives the actual stronger dyadic mask, with precisely
its nonzero all-zero survival probability as weight. -/
theorem structuredPlusOne_degreeFour_restrictedAlias_eq_maskSurvival
    (tailBits : Nat) (htail : tailBits <= 3) :
    finiteAverage
        (fun seed :
            (Fin (structuredIndependencePlusOne 1 * 3) -> Bool) ×
              (Fin (structuredIndependencePlusOne 1 * 3) -> Bool) =>
          restrictedCharacterAverage plusOneLeft
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed.1)
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed.2) *
            restrictedCharacterAverage plusOneRight
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed.1)
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed.2)) =
      finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne 1 * 3) -> Bool =>
          maskAllZeroIndicator plusOneDualWord
            (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
              seed)) := by
  rw [structuredUnbiasedSourcePlusOne_restrictedCharacterPairMoment_eq]
  rw [plusOneLeft_symmDiff_plusOneRight,
    if_pos plusOneDualWord_isStructuredDualSupport,
    plusOneLeft_union_plusOneRight, one_mul]

theorem structuredPlusOne_degreeFour_restrictedAlias_pos
    (tailBits : Nat) (htail : tailBits <= 3) :
    0 < finiteAverage
        (fun seed :
            (Fin (structuredIndependencePlusOne 1 * 3) -> Bool) ×
              (Fin (structuredIndependencePlusOne 1 * 3) -> Bool) =>
          restrictedCharacterAverage plusOneLeft
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed.1)
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed.2) *
            restrictedCharacterAverage plusOneRight
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed.1)
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed.2)) := by
  rw [structuredPlusOne_degreeFour_restrictedAlias_eq_maskSurvival]
  exact structuredDyadicSourcePlusOne_maskSurvival_pos
    3 1 tailBits (by omega) htail plusOneDualWord

/-- Therefore `4m+2` does not diagonalize all degrees above `2m+1`. -/
theorem not_structuredUnbiasedSourcePlusOne_strictAboveBottom_gramOrthogonal :
    ¬ (∀ left right : Finset EightCoordinate,
        3 < left.card -> 3 < right.card -> left ≠ right ->
          finiteAverage
              (fun seed : Fin (structuredIndependencePlusOne 1 * 3) -> Bool =>
                character left
                    (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed) *
                  character right
                    (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed)) =
            0) := by
  intro horthogonal
  have hzero := horthogonal plusOneLeft plusOneRight
    (by rw [plusOneLeft_card]; omega) (by rw [plusOneRight_card]; omega)
    plusOneLeft_ne_plusOneRight
  rw [structuredUnbiasedSourcePlusOne_degreeFour_alias_eq_one] at hzero
  norm_num at hzero

/-! ## Item (c): a finite Boolean cone carrying the surviving alias -/

/-- The intersection of the two parity half-cubes selected by the surviving
degree-four pair.  It is written as a rational function to expose its Fourier
coefficients. -/
def plusOneBooleanConeIndicator (input : EightCoordinate -> Bool) : Rat :=
  ((1 + character plusOneLeft input) / 2) *
    ((1 + character plusOneRight input) / 2)

/-- The cone indicator is genuinely Boolean-valued. -/
theorem plusOneBooleanConeIndicator_eq_zero_or_one
    (input : EightCoordinate -> Bool) :
    plusOneBooleanConeIndicator input = 0 ∨
      plusOneBooleanConeIndicator input = 1 := by
  have hleft := character_square plusOneLeft input
  have hright := character_square plusOneRight input
  have hleftIdem :
      ((1 + character plusOneLeft input) / 2) *
          ((1 + character plusOneLeft input) / 2) =
        (1 + character plusOneLeft input) / 2 := by
    nlinarith
  have hrightIdem :
      ((1 + character plusOneRight input) / 2) *
          ((1 + character plusOneRight input) / 2) =
        (1 + character plusOneRight input) / 2 := by
    nlinarith
  have hidem :
      plusOneBooleanConeIndicator input *
          plusOneBooleanConeIndicator input =
        plusOneBooleanConeIndicator input := by
    unfold plusOneBooleanConeIndicator
    calc
      (((1 + character plusOneLeft input) / 2) *
            ((1 + character plusOneRight input) / 2)) *
          (((1 + character plusOneLeft input) / 2) *
            ((1 + character plusOneRight input) / 2)) =
        (((1 + character plusOneLeft input) / 2) *
            ((1 + character plusOneLeft input) / 2)) *
          (((1 + character plusOneRight input) / 2) *
            ((1 + character plusOneRight input) / 2)) := by ring
      _ = _ := by rw [hleftIdem, hrightIdem]
  have hfactor :
      plusOneBooleanConeIndicator input *
          (plusOneBooleanConeIndicator input - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (sub_eq_zero.mp hone)

private theorem finiteAverage_add_plusOne
    {Seed : Type*} [Fintype Seed] (left right : Seed -> Rat) :
    finiteAverage (fun seed => left seed + right seed) =
      finiteAverage left + finiteAverage right := by
  unfold finiteAverage
  rw [Finset.sum_add_distrib]
  ring

/-- The exact four-character Fourier spectrum of the Boolean cone. -/
theorem coefficient_plusOneBooleanConeIndicator
    (test : Finset EightCoordinate) :
    coefficient plusOneBooleanConeIndicator test =
      (1 / 4 : Rat) * (if (∅ : Finset EightCoordinate) = test then 1 else 0) +
      (1 / 4 : Rat) * (if plusOneLeft = test then 1 else 0) +
      (1 / 4 : Rat) * (if plusOneRight = test then 1 else 0) +
      (1 / 4 : Rat) *
        (if plusOneLeft ∆ plusOneRight = test then 1 else 0) := by
  rw [coefficient_eq_finiteAverage_mul]
  calc
    finiteAverage (fun input : EightCoordinate -> Bool =>
        plusOneBooleanConeIndicator input * character test input) =
      finiteAverage (fun input : EightCoordinate -> Bool =>
        (1 / 4 : Rat) *
            (character ∅ input * character test input) +
          (1 / 4 : Rat) *
            (character plusOneLeft input * character test input) +
          (1 / 4 : Rat) *
            (character plusOneRight input * character test input) +
          (1 / 4 : Rat) *
            (character (plusOneLeft ∆ plusOneRight) input *
              character test input)) := by
          apply finiteAverage_congr
          intro input
          unfold plusOneBooleanConeIndicator
          rw [← character_mul_character_eq_symmDiff
            plusOneLeft plusOneRight input]
          simp only [character_empty]
          ring
    _ = (1 / 4 : Rat) * finiteAverage (fun input : EightCoordinate -> Bool =>
          character ∅ input * character test input) +
        (1 / 4 : Rat) * finiteAverage (fun input : EightCoordinate -> Bool =>
          character plusOneLeft input * character test input) +
        (1 / 4 : Rat) * finiteAverage (fun input : EightCoordinate -> Bool =>
          character plusOneRight input * character test input) +
        (1 / 4 : Rat) * finiteAverage (fun input : EightCoordinate -> Bool =>
          character (plusOneLeft ∆ plusOneRight) input *
            character test input) := by
          rw [finiteAverage_add_plusOne, finiteAverage_add_plusOne,
            finiteAverage_add_plusOne,
            finiteAverage_const_mul, finiteAverage_const_mul,
            finiteAverage_const_mul, finiteAverage_const_mul]
    _ = _ := by
      rw [finiteAverage_character_mul_character,
        finiteAverage_character_mul_character,
        finiteAverage_character_mul_character,
        finiteAverage_character_mul_character]

theorem plusOneLeft_nonempty : plusOneLeft ≠ ∅ := by
  intro hempty
  have hcard := plusOneLeft_card
  rw [hempty] at hcard
  simp at hcard

theorem plusOneRight_nonempty : plusOneRight ≠ ∅ := by
  intro hempty
  have hcard := plusOneRight_card
  rw [hempty] at hcard
  simp at hcard

theorem plusOneDualWord_ne_plusOneLeft : plusOneDualWord ≠ plusOneLeft := by
  intro hequal
  have hcard := plusOneDualWord_card
  rw [hequal, plusOneLeft_card] at hcard
  omega

theorem plusOneDualWord_ne_plusOneRight : plusOneDualWord ≠ plusOneRight := by
  intro hequal
  have hcard := plusOneDualWord_card
  rw [hequal, plusOneRight_card] at hcard
  omega

theorem coefficient_plusOneBooleanConeIndicator_left :
    coefficient plusOneBooleanConeIndicator plusOneLeft = (1 / 4 : Rat) := by
  rw [coefficient_plusOneBooleanConeIndicator,
    plusOneLeft_symmDiff_plusOneRight]
  have hemptyNe : (∅ : Finset EightCoordinate) ≠ plusOneLeft :=
    Ne.symm plusOneLeft_nonempty
  have hrightNe : plusOneRight ≠ plusOneLeft :=
    Ne.symm plusOneLeft_ne_plusOneRight
  simp [hemptyNe, hrightNe, plusOneDualWord_ne_plusOneLeft]

theorem coefficient_plusOneBooleanConeIndicator_right :
    coefficient plusOneBooleanConeIndicator plusOneRight = (1 / 4 : Rat) := by
  rw [coefficient_plusOneBooleanConeIndicator,
    plusOneLeft_symmDiff_plusOneRight]
  have hemptyNe : (∅ : Finset EightCoordinate) ≠ plusOneRight :=
    Ne.symm plusOneRight_nonempty
  simp [hemptyNe, plusOneLeft_ne_plusOneRight,
    plusOneDualWord_ne_plusOneRight]

/-- The explicit Boolean cone has a positive `1/16` off-diagonal base Gram
contribution in degrees `(4,4)`.  This refutes a full-tail diagonal argument;
it is not, by itself, a violation of a larger numerical high-tail bound. -/
theorem plusOneBooleanConeIndicator_offDiagonalBaseContribution_eq :
    coefficient plusOneBooleanConeIndicator plusOneLeft *
        coefficient plusOneBooleanConeIndicator plusOneRight *
      finiteAverage
        (fun seed : Fin (structuredIndependencePlusOne 1 * 3) -> Bool =>
          character plusOneLeft
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed) *
            character plusOneRight
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed)) =
      (1 / 16 : Rat) := by
  rw [coefficient_plusOneBooleanConeIndicator_left,
    coefficient_plusOneBooleanConeIndicator_right,
    structuredUnbiasedSourcePlusOne_degreeFour_alias_eq_one]
  norm_num

/-- After the stronger structured mask, the same Boolean-cone term is
exactly `1/16` times the eight-point mask-survival probability. -/
theorem plusOneBooleanConeIndicator_offDiagonalRestrictedContribution_eq
    (tailBits : Nat) (htail : tailBits <= 3) :
    coefficient plusOneBooleanConeIndicator plusOneLeft *
        coefficient plusOneBooleanConeIndicator plusOneRight *
      finiteAverage
        (fun seed :
            (Fin (structuredIndependencePlusOne 1 * 3) -> Bool) ×
              (Fin (structuredIndependencePlusOne 1 * 3) -> Bool) =>
          restrictedCharacterAverage plusOneLeft
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed.1)
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed.2) *
            restrictedCharacterAverage plusOneRight
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed.1)
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed.2)) =
      (1 / 16 : Rat) *
        finiteAverage
          (fun seed : Fin (structuredIndependencePlusOne 1 * 3) -> Bool =>
            maskAllZeroIndicator plusOneDualWord
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed)) := by
  rw [coefficient_plusOneBooleanConeIndicator_left,
    coefficient_plusOneBooleanConeIndicator_right,
    structuredPlusOne_degreeFour_restrictedAlias_eq_maskSurvival]
  ring

/-- In particular, the complete base-plus-mask off-diagonal cone term is
strictly positive for every legal dyadic tail width. -/
theorem plusOneBooleanConeIndicator_offDiagonalRestrictedContribution_pos
    (tailBits : Nat) (htail : tailBits <= 3) :
    0 < coefficient plusOneBooleanConeIndicator plusOneLeft *
        coefficient plusOneBooleanConeIndicator plusOneRight *
      finiteAverage
        (fun seed :
            (Fin (structuredIndependencePlusOne 1 * 3) -> Bool) ×
              (Fin (structuredIndependencePlusOne 1 * 3) -> Bool) =>
          restrictedCharacterAverage plusOneLeft
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed.1)
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed.2) *
            restrictedCharacterAverage plusOneRight
              (structuredUnbiasedSourcePlusOne 3 1 (by omega) seed.1)
              (structuredDyadicSourcePlusOne 3 1 tailBits (by omega) htail
                seed.2)) := by
  rw [plusOneBooleanConeIndicator_offDiagonalRestrictedContribution_eq]
  exact mul_pos (by norm_num)
    (structuredDyadicSourcePlusOne_maskSurvival_pos
      3 1 tailBits (by omega) htail plusOneDualWord)


end DPTWStructuredIndependencePlusOneNoGo

end

end OneTapeMagnification
end Frontier
end Pnp4
