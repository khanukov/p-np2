import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependenceFarTail
import Mathlib.Algebra.Group.AddChar

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# The dual code of the structured unbiased polynomial source

The unbiased DPTW source is obtained by evaluating a uniformly random
bounded-degree polynomial over `GF(2^n)` and exposing one fixed Boolean
coordinate of every value.  Consequently, the Walsh sign of an arbitrary
support is an additive character of the coefficient space.  This file makes
that character explicit and applies finite-group character orthogonality.

Unlike bounded-independence, the resulting formula is valid at every degree:
the only surviving supports are the dual-code supports on which the induced
character is trivial.  This is lower-layer infrastructure; it does not reduce
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanBoundedIndependenceFarTail
open FiniteBooleanFourierEnergy
open FiniteUnambiguousFBDD
open FiniteBooleanFullIndependenceRestriction
open DPTWFiniteFieldKWiseSeed
open GaloisBilinearTensorBridge
open DPTWStructuredFieldCoordinatePrimitive

namespace DPTWStructuredUnbiasedDualCode

/-- The Boolean coordinate exposed by the `t = 1` structured source. -/
def structuredEvaluationBit
    (n k : Nat) (hn : 0 < n)
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k)
    (index : Fin (2 ^ n)) : Bool :=
  gfTwoBoolCoordinates n (Nat.ne_of_gt hn)
    (polynomial.1.eval
      (structuredTruthTableNode n (Nat.ne_of_gt hn) index))
    ⟨0, hn⟩

@[simp]
theorem structuredEvaluationBit_zero
    (n k : Nat) (hn : 0 < n) (index : Fin (2 ^ n)) :
    structuredEvaluationBit n k hn 0 index = false := by
  simp [structuredEvaluationBit]

@[simp]
theorem structuredEvaluationBit_add
    (n k : Nat) (hn : 0 < n)
    (left right : Polynomial.degreeLT (GaloisField 2 n) k)
    (index : Fin (2 ^ n)) :
    structuredEvaluationBit n k hn (left + right) index =
      Bool.xor (structuredEvaluationBit n k hn left index)
        (structuredEvaluationBit n k hn right index) := by
  unfold structuredEvaluationBit
  rw [show (left + right).1.eval
        (structuredTruthTableNode n (Nat.ne_of_gt hn) index) =
      left.1.eval (structuredTruthTableNode n (Nat.ne_of_gt hn) index) +
        right.1.eval (structuredTruthTableNode n (Nat.ne_of_gt hn) index) by
      simp]
  exact gfTwoBoolCoordinates_add n (Nat.ne_of_gt hn) _ _ ⟨0, hn⟩

/-- The Walsh sign on `support`, regarded as an additive character of the
bounded-degree polynomial coefficient space. -/
def structuredSupportAddChar
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    AddChar (Polynomial.degreeLT (GaloisField 2 n) k) Rat where
  toFun polynomial :=
    character support (structuredEvaluationBit n k hn polynomial)
  map_zero_eq_one' := by
    simp [character]
  map_add_eq_mul' left right := by
    rw [← FiniteBooleanRestrictionMoment.character_xor support
      (structuredEvaluationBit n k hn left)
      (structuredEvaluationBit n k hn right)]
    congr 1
    funext index
    exact structuredEvaluationBit_add n k hn left right index

/-- A support belongs to the exact dual code when its induced character on
all degree-`< k` polynomials is trivial. -/
def IsStructuredDualSupport
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) : Prop :=
  structuredSupportAddChar n k hn support = 0

local instance structuredDualSupportDecidable
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    Decidable (IsStructuredDualSupport n k hn support) :=
  Classical.propDecidable _

theorem isStructuredDualSupport_iff
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    IsStructuredDualSupport n k hn support ↔
      ∀ polynomial : Polynomial.degreeLT (GaloisField 2 n) k,
        character support (structuredEvaluationBit n k hn polynomial) = 1 := by
  exact AddChar.eq_zero_iff

/-- Finite-group character orthogonality for the structured Walsh
character, before transporting through the Boolean seed equivalence. -/
theorem finiteAverage_structuredSupportAddChar
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    finiteAverage (fun polynomial :
        Polynomial.degreeLT (GaloisField 2 n) k =>
      character support (structuredEvaluationBit n k hn polynomial)) =
      if IsStructuredDualSupport n k hn support then 1 else 0 := by
  classical
  unfold finiteAverage IsStructuredDualSupport
  change
    (∑ polynomial : Polynomial.degreeLT (GaloisField 2 n) k,
        structuredSupportAddChar n k hn support polynomial) /
      (Fintype.card (Polynomial.degreeLT (GaloisField 2 n) k) : Rat) = _
  rw [AddChar.sum_eq_ite (structuredSupportAddChar n k hn support)]
  split_ifs with h
  · have hcard : Fintype.card
        (Polynomial.degreeLT (GaloisField 2 n) k) ≠ 0 :=
      Fintype.card_ne_zero
    field_simp
  · simp

/-! ## Transport to the actual circuit generator -/

/-- For a one-bit prefix, membership in the false set is exactly vanishing
of the first chosen-basis coordinate. -/
theorem mem_zeroPrefixFalseSet_one_iff
    (n : Nat) (hn : 0 < n) (value : GaloisField 2 n) :
    value ∈ zeroPrefixFalseSet n 1 (Nat.ne_of_gt hn) (by omega) ↔
      gfTwoBoolCoordinates n (Nat.ne_of_gt hn) value ⟨0, hn⟩ = false := by
  rw [mem_zeroPrefixFalseSet]
  constructor
  · intro h
    simpa [prefixPosition] using h (0 : Fin 1)
  · intro h index
    have hindex : index = 0 := Subsingleton.elim _ _
    subst index
    simpa [prefixPosition] using h

/-- Thresholding by the one-bit zero-prefix set returns precisely the
exposed evaluation bit. -/
theorem structuredPolynomialSubsetSource_one_eq_evaluationBit
    (n k : Nat) (hn : 0 < n)
    (seed : Fin (k * n) → Bool) (index : Fin (2 ^ n)) :
    structuredPolynomialSubsetSource n k (Nat.ne_of_gt hn)
        (zeroPrefixFalseSet n 1 (Nat.ne_of_gt hn) (by omega)) seed index =
      structuredEvaluationBit n k hn
        (structuredPolynomialBitSeedEquiv k n (Nat.ne_of_gt hn) seed) index := by
  classical
  unfold structuredPolynomialSubsetSource polynomialSubsetSource
  let value : GaloisField 2 n :=
    (structuredPolynomialBitSeedEquiv k n (Nat.ne_of_gt hn) seed).1.eval
      (structuredTruthTableNode n (Nat.ne_of_gt hn) index)
  change fieldSubsetCoin
      (zeroPrefixFalseSet n 1 (Nat.ne_of_gt hn) (by omega)) value =
    gfTwoBoolCoordinates n (Nat.ne_of_gt hn) value ⟨0, hn⟩
  have hmem := mem_zeroPrefixFalseSet_one_iff n hn value
  cases hbit : gfTwoBoolCoordinates n (Nat.ne_of_gt hn) value ⟨0, hn⟩ <;>
    simp_all [fieldSubsetCoin]

/-- The actual structured unbiased coordinate generator is the exposed
evaluation-bit source, under the explicit structured seed equivalence. -/
theorem structuredUnbiasedPrimitive_generate_eq_evaluationBit
    (n m : Nat) (hn : 0 < n)
    (seed : Fin (structuredIndependence m * n) → Bool)
    (index : Fin (2 ^ n)) :
    (structuredUnbiasedPrimitive n m hn).generate seed index =
      structuredEvaluationBit n (structuredIndependence m) hn
        (structuredPolynomialBitSeedEquiv
          (structuredIndependence m) n (Nat.ne_of_gt hn) seed) index := by
  change (structuredDyadicPrimitive n m 1 hn (by omega)).generate seed index = _
  rw [structuredDyadicPrimitive_generate]
  exact structuredPolynomialSubsetSource_one_eq_evaluationBit
    n (structuredIndependence m) hn seed index

/-- Exact arbitrary-degree Walsh law of the actual structured generator:
the expectation is one exactly on its dual code, and zero everywhere else. -/
theorem structuredUnbiasedPrimitive_characterAverage_eq_dualIndicator
    (n m : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
      character support
        ((structuredUnbiasedPrimitive n m hn).generate seed)) =
      if IsStructuredDualSupport n (structuredIndependence m) hn support
        then 1 else 0 := by
  calc
    finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        character support
          ((structuredUnbiasedPrimitive n m hn).generate seed)) =
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
        character support
          (structuredEvaluationBit n (structuredIndependence m) hn
            (structuredPolynomialBitSeedEquiv
              (structuredIndependence m) n (Nat.ne_of_gt hn) seed))) := by
        apply finiteAverage_congr
        intro seed
        congr 1
        funext index
        exact structuredUnbiasedPrimitive_generate_eq_evaluationBit
          n m hn seed index
    _ = finiteAverage (fun polynomial :
          Polynomial.degreeLT (GaloisField 2 n) (structuredIndependence m) =>
        character support
          (structuredEvaluationBit n (structuredIndependence m) hn polynomial)) := by
        simpa using
          (DPTWFiniteFieldKWiseSeed.finiteAverage_comp_equiv
            (structuredPolynomialBitSeedEquiv
              (structuredIndependence m) n (Nat.ne_of_gt hn))
            (fun polynomial : Polynomial.degreeLT
                (GaloisField 2 n) (structuredIndependence m) =>
              character support
                (structuredEvaluationBit n (structuredIndependence m) hn
                  polynomial)))
    _ = _ := finiteAverage_structuredSupportAddChar
      n (structuredIndependence m) hn support

/-- Arbitrary-support Gram entries of the actual source are the indicator of
the dual-code condition on the symmetric difference.  Thus the far-tail
residual can be narrowed from all far pairs to dual-code far pairs. -/
theorem structuredUnbiasedPrimitive_characterPairAverage_eq_dualIndicator
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n))) :
    finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool =>
      character left ((structuredUnbiasedPrimitive n m hn).generate seed) *
        character right ((structuredUnbiasedPrimitive n m hn).generate seed)) =
      if IsStructuredDualSupport n (structuredIndependence m) hn
          (left ∆ right)
        then 1 else 0 := by
  calc
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) → Bool =>
          character left ((structuredUnbiasedPrimitive n m hn).generate seed) *
            character right
              ((structuredUnbiasedPrimitive n m hn).generate seed)) =
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) → Bool =>
          character (left ∆ right)
            ((structuredUnbiasedPrimitive n m hn).generate seed)) := by
        apply finiteAverage_congr
        intro seed
        exact character_mul_character_eq_symmDiff left right
          ((structuredUnbiasedPrimitive n m hn).generate seed)
    _ = _ := structuredUnbiasedPrimitive_characterAverage_eq_dualIndicator
      n m hn (left ∆ right)

/-! ## Dual-code support of the restricted-character far tail -/

/-- With the structured unbiased source in the base half, an arbitrary
restricted-character pair moment is exactly its dual-code indicator times
the mask-survival probability.  No bounded-independence cutoff is needed for
this identity. -/
theorem structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq
    (n m : Nat) (hn : 0 < n)
    {TSeed : Type*} [Fintype TSeed] [Nonempty TSeed]
    (T : TSeed → Fin (2 ^ n) → Bool)
    (left right : Finset (Fin (2 ^ n))) :
    finiteAverage (fun seed :
        (Fin (structuredIndependence m * n) → Bool) × TSeed =>
      restrictedCharacterAverage left
          ((structuredUnbiasedPrimitive n m hn).generate seed.1) (T seed.2) *
        restrictedCharacterAverage right
          ((structuredUnbiasedPrimitive n m hn).generate seed.1) (T seed.2)) =
      (if IsStructuredDualSupport n (structuredIndependence m) hn
          (left ∆ right) then 1 else 0) *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator (left ∪ right) (T t)) := by
  rw [restrictedCharacterAverage_pairMoment_eq]
  rw [structuredUnbiasedPrimitive_characterAverage_eq_dualIndicator]

/-- The exact structured far residual.  In comparison with the generic
bounded-independence residual, only pairs whose symmetric difference lies in
the finite-field dual code remain, and their base correlation has disappeared
because it is exactly one. -/
noncomputable def structuredDualFarPairCorrelation
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) : Rat :=
  ∑ left ∈ highDegreeSupports (2 ^ n) cutoff,
    ∑ right ∈ highDegreeSupports (2 ^ n) cutoff,
      if left ≠ right ∧
          structuredIndependence m < (left ∆ right).card ∧
          IsStructuredDualSupport n (structuredIndependence m) hn
            (left ∆ right) then
        coefficient f left * coefficient f right *
          finiteAverage
            (fun t : Fin (structuredIndependence m * n) → Bool =>
              maskAllZeroIndicator (left ∪ right)
                ((structuredDyadicPrimitive n m tailBits hn htail).generate t))
      else 0

/-- The generic far correlation of the actual structured pair is exactly the
dual-only residual above. -/
theorem structured_highTailFarPairCorrelation_eq_dual
    (n m tailBits cutoff : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    highTailFarPairCorrelation f cutoff (structuredIndependence m)
        (structuredUnbiasedPrimitive n m hn).generate
        (structuredDyadicPrimitive n m tailBits hn htail).generate =
      structuredDualFarPairCorrelation n m tailBits cutoff hn htail f := by
  classical
  unfold highTailFarPairCorrelation structuredDualFarPairCorrelation
  apply Finset.sum_congr rfl
  intro left hleft
  apply Finset.sum_congr rfl
  intro right hright
  by_cases hfar : left ≠ right ∧
      structuredIndependence m < (left ∆ right).card
  · by_cases hdual : IsStructuredDualSupport n
        (structuredIndependence m) hn (left ∆ right)
    · rw [if_pos hfar, if_pos ⟨hfar.1, hfar.2, hdual⟩,
        structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq]
      simp [hdual]
    · rw [if_pos hfar,
        if_neg (by
          intro h
          exact hdual h.2.2),
        structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq]
      simp [hdual]
  · rw [if_neg hfar]
    have hcombined : ¬ (left ≠ right ∧
        structuredIndependence m < (left ∆ right).card ∧
        IsStructuredDualSupport n (structuredIndependence m) hn
          (left ∆ right)) := by
      intro h
      exact hfar ⟨h.1, h.2.1⟩
    rw [if_neg hcombined]

/-- At the DPTW cutoff `2m`, the exact structured second moment consists of
the diagonal mask-survival energy and only the dual-code far residual. -/
theorem structured_highTail_restriction_secondMoment_eq_diagonal_add_dual
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) → Bool) → Rat) :
    finiteAverage (fun seed :
        (Fin (structuredIndependence m * n) → Bool) ×
          (Fin (structuredIndependence m * n) → Bool) =>
      (finiteAverage (fun uniform : Fin (2 ^ n) → Bool =>
        ratHighDegreeFourierTail f (2 * m)
          (maskedInput
            ((structuredUnbiasedPrimitive n m hn).generate seed.1)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed.2)
            uniform))) ^ 2) =
      (∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
        (coefficient f support) ^ 2 *
          finiteAverage
            (fun t : Fin (structuredIndependence m * n) → Bool =>
              maskAllZeroIndicator support
                ((structuredDyadicPrimitive n m tailBits hn htail).generate t))) +
        structuredDualFarPairCorrelation n m tailBits (2 * m)
          hn htail f := by
  rw [highTail_restriction_secondMoment_eq_diagonal_add_far]
  · rw [structured_highTailFarPairCorrelation_eq_dual]
  · exact structuredUnbiasedPrimitive_patternUnbiased n m hn

/-! ## Explicit Reed--Solomon parity checks -/

/-- The `exponent`-th power sum of the structured evaluation nodes selected
by a Boolean support. -/
def structuredSupportPowerSum
    (n : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (exponent : Nat) : GaloisField 2 n :=
  ∑ index ∈ support,
    structuredTruthTableNode n (Nat.ne_of_gt hn) index ^ exponent

/-- Sum of a bounded-degree polynomial over all selected evaluation nodes. -/
def structuredSupportEvaluationSum
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k) :
    GaloisField 2 n :=
  ∑ index ∈ support,
    polynomial.1.eval
      (structuredTruthTableNode n (Nat.ne_of_gt hn) index)

/-- Summing polynomial evaluations exchanges the node sum with the bounded
coefficient expansion. -/
theorem structuredSupportEvaluationSum_eq_coefficients_powerSums
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k) :
    structuredSupportEvaluationSum n k hn support polynomial =
      ∑ exponent : Fin k,
        Polynomial.degreeLTEquiv (GaloisField 2 n) k polynomial exponent *
          structuredSupportPowerSum n hn support exponent.val := by
  classical
  unfold structuredSupportEvaluationSum structuredSupportPowerSum
  calc
    (∑ index ∈ support,
        polynomial.1.eval
          (structuredTruthTableNode n (Nat.ne_of_gt hn) index)) =
      ∑ index ∈ support, ∑ exponent : Fin k,
        Polynomial.degreeLTEquiv (GaloisField 2 n) k polynomial exponent *
          structuredTruthTableNode n (Nat.ne_of_gt hn) index ^ exponent.val := by
            apply Finset.sum_congr rfl
            intro index hindex
            exact Polynomial.eval_eq_sum_degreeLTEquiv polynomial.2 _
    _ = ∑ exponent : Fin k, ∑ index ∈ support,
        Polynomial.degreeLTEquiv (GaloisField 2 n) k polynomial exponent *
          structuredTruthTableNode n (Nat.ne_of_gt hn) index ^ exponent.val := by
            rw [Finset.sum_comm]
    _ = ∑ exponent : Fin k,
        Polynomial.degreeLTEquiv (GaloisField 2 n) k polynomial exponent *
          ∑ index ∈ support,
            structuredTruthTableNode n (Nat.ne_of_gt hn) index ^
              exponent.val := by
            apply Finset.sum_congr rfl
            intro exponent hexponent
            rw [Finset.mul_sum]

/-- The support Walsh character is the sign of the exposed coordinate of
the total field-valued evaluation sum. -/
theorem character_structuredEvaluationBit_eq_evaluationSumSign
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k) :
    character support (structuredEvaluationBit n k hn polynomial) =
      boolSign
        (gfTwoBoolCoordinates n (Nat.ne_of_gt hn)
          (structuredSupportEvaluationSum n k hn support polynomial)
          ⟨0, hn⟩) := by
  classical
  induction support using Finset.induction_on with
  | empty => simp [character, structuredSupportEvaluationSum]
  | @insert index support hindex ih =>
      rw [character, Finset.prod_insert hindex]
      change boolSign (structuredEvaluationBit n k hn polynomial index) *
          character support (structuredEvaluationBit n k hn polynomial) = _
      rw [ih]
      unfold structuredSupportEvaluationSum
      rw [Finset.sum_insert hindex, gfTwoBoolCoordinates_add,
        FiniteBooleanRestrictionMoment.boolSign_xor]
      rfl

/-- A bounded-degree polynomial with one prescribed coefficient. -/
def structuredSingleCoefficientPolynomial
    (n k : Nat) (exponent : Fin k) (coefficientValue : GaloisField 2 n) :
    Polynomial.degreeLT (GaloisField 2 n) k :=
  (Polynomial.degreeLTEquiv (GaloisField 2 n) k).symm
    (Pi.single exponent coefficientValue)

/-- Evaluation of the one-coefficient polynomial is its single monomial. -/
theorem structuredSingleCoefficientPolynomial_eval
    (n k : Nat) (exponent : Fin k) (coefficientValue point : GaloisField 2 n) :
    (structuredSingleCoefficientPolynomial n k exponent coefficientValue).1.eval point =
      coefficientValue * point ^ exponent.val := by
  rw [Polynomial.eval_eq_sum_degreeLTEquiv
    (structuredSingleCoefficientPolynomial n k exponent coefficientValue).2]
  simp [structuredSingleCoefficientPolynomial, Pi.single_apply]

/-- Its support-evaluation sum isolates one power sum. -/
theorem structuredSupportEvaluationSum_singleCoefficient
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (exponent : Fin k) (coefficientValue : GaloisField 2 n) :
    structuredSupportEvaluationSum n k hn support
        (structuredSingleCoefficientPolynomial n k exponent coefficientValue) =
      coefficientValue * structuredSupportPowerSum n hn support exponent.val := by
  classical
  unfold structuredSupportEvaluationSum structuredSupportPowerSum
  simp_rw [structuredSingleCoefficientPolynomial_eval]
  rw [Finset.mul_sum]

@[simp]
theorem boolSign_eq_one_iff (value : Bool) :
    boolSign value = 1 ↔ value = false := by
  cases value <;> norm_num [boolSign]

/-- A field element whose exposed chosen-basis coordinate is `true`. -/
def exposedCoordinateWitness (n : Nat) (hn : 0 < n) : GaloisField 2 n :=
  (gfTwoBoolCoordinates n (Nat.ne_of_gt hn)).symm
    (Function.update (fun _ => false) ⟨0, hn⟩ true)

@[simp]
theorem exposedCoordinateWitness_bit (n : Nat) (hn : 0 < n) :
    gfTwoBoolCoordinates n (Nat.ne_of_gt hn)
        (exposedCoordinateWitness n hn) ⟨0, hn⟩ = true := by
  unfold exposedCoordinateWitness
  rw [Equiv.apply_symm_apply]
  simp

/-- Nondegeneracy of the exposed coordinate after allowing arbitrary field
multipliers.  If every multiple has exposed bit zero, the element is zero. -/
theorem eq_zero_of_exposedCoordinate_mul_eq_false
    (n : Nat) (hn : 0 < n) (value : GaloisField 2 n)
    (hvanish : ∀ scalar : GaloisField 2 n,
      gfTwoBoolCoordinates n (Nat.ne_of_gt hn) (scalar * value) ⟨0, hn⟩ =
        false) :
    value = 0 := by
  by_contra hvalue
  let scalar : GaloisField 2 n := exposedCoordinateWitness n hn * value⁻¹
  have hproduct : scalar * value = exposedCoordinateWitness n hn := by
    simp [scalar, hvalue]
  have := hvanish scalar
  rw [hproduct, exposedCoordinateWitness_bit] at this
  contradiction

/-- Exact trace-RS/subfield-subcode parity-check characterization: a support
is dual precisely when all node power sums below the polynomial degree bound
vanish in `GF(2^n)`. -/
theorem isStructuredDualSupport_iff_powerSums_eq_zero
    (n k : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n))) :
    IsStructuredDualSupport n k hn support ↔
      ∀ exponent : Fin k,
        structuredSupportPowerSum n hn support exponent.val = 0 := by
  constructor
  · intro hdual exponent
    apply eq_zero_of_exposedCoordinate_mul_eq_false n hn
    intro scalar
    have hcharacter :=
      (isStructuredDualSupport_iff n k hn support).mp hdual
        (structuredSingleCoefficientPolynomial n k exponent scalar)
    rw [character_structuredEvaluationBit_eq_evaluationSumSign,
      boolSign_eq_one_iff,
      structuredSupportEvaluationSum_singleCoefficient] at hcharacter
    exact hcharacter
  · intro hpower
    rw [isStructuredDualSupport_iff]
    intro polynomial
    rw [character_structuredEvaluationBit_eq_evaluationSumSign,
      boolSign_eq_one_iff]
    have hsum : structuredSupportEvaluationSum n k hn support polynomial = 0 := by
      rw [structuredSupportEvaluationSum_eq_coefficients_powerSums]
      apply Finset.sum_eq_zero
      intro exponent hexponent
      rw [hpower exponent, mul_zero]
    rw [hsum]
    simp

/-- The bounded-independence guarantee is the minimum-distance corollary of
the exact dual-code law: no nonempty support of size at most `4m+1` is dual. -/
theorem not_isStructuredDualSupport_of_nonempty_card_le
    (n m : Nat) (hn : 0 < n) (support : Finset (Fin (2 ^ n)))
    (hcard : support.card ≤ structuredIndependence m)
    (hnonempty : support.Nonempty) :
    ¬ IsStructuredDualSupport n (structuredIndependence m) hn support := by
  intro hdual
  have hzero :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) → Bool =>
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)) = 0 :=
    character_average_eq_zero_of_patternUnbiased
      (structuredUnbiasedPrimitive n m hn).generate
      (structuredUnbiasedPrimitive_patternUnbiased n m hn)
      support hcard hnonempty
  have hone :
      finiteAverage
          (fun seed : Fin (structuredIndependence m * n) → Bool =>
            character support
              ((structuredUnbiasedPrimitive n m hn).generate seed)) = 1 := by
    rw [structuredUnbiasedPrimitive_characterAverage_eq_dualIndicator,
      if_pos hdual]
  linarith

end DPTWStructuredUnbiasedDualCode
end
end OneTapeMagnification
end Frontier
end Pnp4
