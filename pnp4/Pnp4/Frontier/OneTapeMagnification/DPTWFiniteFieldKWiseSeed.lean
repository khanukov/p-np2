import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Lagrange

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite-field bounded-independence seeds

This file isolates the short-seed probability layer of the polynomial
evaluation construction used in DPTW Claim 3.11.  A uniformly random
polynomial of degree below `k` over `GF(2^d)` is evaluated at distinct field
points, and a fixed field subset is declared false.  The resulting Boolean
source has exact `k`-wise product cylinder laws.

The final source is transported to a flat Boolean tape of exactly `k * d`
bits.  That transport and the false subset are classically chosen.  In
particular, this module does **not** give a local decoder or a small joint
coordinate circuit; it only closes the exact finite-law and seed-cardinality
layer.  Hence this is lower-layer infrastructure, not a reduction of
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.
-/

noncomputable section

open scoped BigOperators

open Polynomial
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence

namespace DPTWFiniteFieldKWiseSeed

/-! ## Uniformity under a surjective additive map -/

/-- Rational finite averages are invariant under a finite equivalence. -/
theorem finiteAverage_comp_equiv
    {Input Output : Type*} [Fintype Input] [Fintype Output]
    (equiv : Input ≃ Output) (f : Output → ℚ) :
    finiteAverage (fun input ↦ f (equiv input)) = finiteAverage f := by
  unfold finiteAverage
  have hsum :
      (∑ input : Input, f (equiv input)) = ∑ output : Output, f output :=
    Fintype.sum_equiv equiv _ _ (fun _ ↦ rfl)
  rw [hsum, Fintype.card_congr equiv]

/-- A choice of one representative in every fiber splits a surjective
additive homomorphism as its target times its kernel. -/
def surjectiveAddEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (hom : A →+ B) (hsurjective : Function.Surjective hom) :
    A ≃ B × hom.ker := by
  let representative : B → A :=
    fun value ↦ Classical.choose (hsurjective value)
  have hrepresentative : ∀ value, hom (representative value) = value :=
    fun value ↦ Classical.choose_spec (hsurjective value)
  refine
    { toFun := fun input ↦
        (hom input, ⟨input - representative (hom input), ?_⟩)
      invFun := fun output ↦ output.2.1 + representative output.1
      left_inv := ?_
      right_inv := ?_ }
  · simp [hrepresentative]
  · intro input
    simp
  · intro output
    apply Prod.ext
    · change hom (output.2.1 + representative output.1) = output.1
      rw [map_add, output.2.property, hrepresentative, zero_add]
    · apply Subtype.ext
      change
        output.2.1 + representative output.1 -
            representative (hom (output.2.1 + representative output.1)) =
          output.2.1
      rw [map_add, output.2.property, hrepresentative, zero_add]
      simp

/-- Pulling a rational observable back along a surjective homomorphism of
finite additive groups preserves its uniform average. -/
theorem finiteAverage_comp_surjectiveAddHom
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B]
    (hom : A →+ B) (hsurjective : Function.Surjective hom)
    (observable : B → ℚ) :
    finiteAverage (fun input : A ↦ observable (hom input)) =
      finiteAverage observable := by
  classical
  let equiv : A ≃ B × hom.ker := surjectiveAddEquiv hom hsurjective
  calc
    finiteAverage (fun input : A ↦ observable (hom input)) =
        finiteAverage (fun pair : B × hom.ker ↦ observable pair.1) := by
      simpa [equiv, surjectiveAddEquiv] using
        finiteAverage_comp_equiv equiv
          (fun pair : B × hom.ker ↦ observable pair.1)
    _ = finiteAverage observable := by
      unfold finiteAverage
      rw [Fintype.sum_prod_type]
      simp only [Fintype.card_prod, Nat.cast_mul, Finset.sum_const,
        nsmul_eq_mul]
      rw [← Finset.mul_sum]
      have hkernel : (Fintype.card hom.ker : ℚ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      rw [mul_comm (Fintype.card B : ℚ) (Fintype.card hom.ker : ℚ)]
      exact mul_div_mul_left _ _ hkernel

/-! ## Polynomial evaluation on a queried support -/

/-- The coefficient equivalence gives the finite type used for uniform
sampling of bounded-degree polynomials. -/
instance polynomialDegreeLTFintype
    (F : Type*) [Semiring F] [Fintype F] (degreeBound : Nat) :
    Fintype (Polynomial.degreeLT F degreeBound) :=
  Fintype.ofEquiv (Fin degreeBound → F)
    (Polynomial.degreeLTEquiv F degreeBound).symm.toEquiv

/-- A degree-below-`k` polynomial over a finite field has exactly
`|F|^k` possible coefficient vectors. -/
theorem card_polynomialDegreeLT
    (F : Type*) [Semiring F] [Fintype F] (degreeBound : Nat) :
    Fintype.card (Polynomial.degreeLT F degreeBound) =
      Fintype.card F ^ degreeBound := by
  rw [Fintype.card_congr
    (Polynomial.degreeLTEquiv F degreeBound).toEquiv]
  simp

/-- Evaluate a polynomial of degree below `independence` on a finite support
of field nodes. -/
def supportEvaluationLinearMap
    {Coordinate F : Type*} [Field F]
    [DecidableEq Coordinate]
    (nodes : Coordinate → F) (independence : Nat)
    (support : Finset Coordinate) :
    Polynomial.degreeLT F independence →ₗ[F] (support → F) where
  toFun polynomial coordinate := polynomial.1.eval (nodes coordinate.1)
  map_add' left right := by
    funext coordinate
    exact Polynomial.eval_add
  map_smul' scalar polynomial := by
    funext coordinate
    simp

/-- Lagrange interpolation makes support evaluation surjective whenever the
queried nodes are distinct and the support size is at most the degree
parameter. -/
theorem supportEvaluationLinearMap_surjective
    {Coordinate F : Type*} [Field F]
    [DecidableEq Coordinate]
    (nodes : Coordinate → F) (independence : Nat)
    (support : Finset Coordinate)
    (hnodes : Set.InjOn nodes support)
    (hcard : support.card ≤ independence) :
    Function.Surjective
      (supportEvaluationLinearMap nodes independence support) := by
  intro values
  let ambientValues : Coordinate → F := fun coordinate ↦
    if hcoordinate : coordinate ∈ support then
      values ⟨coordinate, hcoordinate⟩
    else 0
  let polynomial : F[X] :=
    Lagrange.interpolate support nodes ambientValues
  have hdegreeSupport : polynomial.degree < support.card := by
    exact Lagrange.degree_interpolate_lt ambientValues hnodes
  have hdegree : polynomial ∈ Polynomial.degreeLT F independence := by
    rw [Polynomial.mem_degreeLT]
    exact hdegreeSupport.trans_le (by exact_mod_cast hcard)
  refine ⟨⟨polynomial, hdegree⟩, ?_⟩
  funext coordinate
  change polynomial.eval (nodes coordinate.1) = values coordinate
  simpa [polynomial, ambientValues] using
    (Lagrange.eval_interpolate_at_node ambientValues hnodes coordinate.2)

/-- Consequently, the evaluation vector on any support of size at most
`independence` is exactly uniform. -/
theorem finiteAverage_supportEvaluation
    {Coordinate F : Type*} [Field F] [Fintype F]
    [DecidableEq Coordinate]
    (nodes : Coordinate → F) (independence : Nat)
    (support : Finset Coordinate)
    (hnodes : Set.InjOn nodes support)
    (hcard : support.card ≤ independence)
    (observable : (support → F) → ℚ) :
    finiteAverage (fun polynomial : Polynomial.degreeLT F independence ↦
      observable (supportEvaluationLinearMap nodes independence support polynomial)) =
    finiteAverage observable := by
  classical
  exact finiteAverage_comp_surjectiveAddHom
    (supportEvaluationLinearMap nodes independence support).toAddMonoidHom
    (supportEvaluationLinearMap_surjective
      nodes independence support hnodes hcard)
    observable

/-! ## Thresholding field values by a fixed subset -/

/-- A field value is false precisely on `falseSet`. -/
def fieldSubsetCoin
    {F : Type*} [DecidableEq F] (falseSet : Finset F) (value : F) : Bool :=
  decide (value ∉ falseSet)

@[simp]
theorem fieldSubsetCoin_eq_false_iff
    {F : Type*} [DecidableEq F] (falseSet : Finset F) (value : F) :
    fieldSubsetCoin falseSet value = false ↔ value ∈ falseSet := by
  simp [fieldSubsetCoin]

@[simp]
theorem fieldSubsetCoin_eq_true_iff
    {F : Type*} [DecidableEq F] (falseSet : Finset F) (value : F) :
    fieldSubsetCoin falseSet value = true ↔ value ∉ falseSet := by
  simp [fieldSubsetCoin]

/-- Exact false mass of subset thresholding. -/
def fieldSubsetFalseMass
    {F : Type*} [Fintype F] (falseSet : Finset F) : ℚ :=
  (falseSet.card : ℚ) / Fintype.card F

theorem finiteAverage_fieldSubsetCoin_false
    {F : Type*} [Fintype F] [DecidableEq F]
    (falseSet : Finset F) :
    finiteAverage (fun value : F ↦
      if fieldSubsetCoin falseSet value = false then (1 : ℚ) else 0) =
      fieldSubsetFalseMass falseSet := by
  unfold finiteAverage fieldSubsetFalseMass
  congr 1
  simp

theorem finiteAverage_fieldSubsetCoin_true
    {F : Type*} [Fintype F] [Nonempty F] [DecidableEq F]
    (falseSet : Finset F) :
    finiteAverage (fun value : F ↦
      if fieldSubsetCoin falseSet value = true then (1 : ℚ) else 0) =
      1 - fieldSubsetFalseMass falseSet := by
  calc
    finiteAverage (fun value : F ↦
        if fieldSubsetCoin falseSet value = true then (1 : ℚ) else 0) =
      finiteAverage (fun value : F ↦
        1 - if fieldSubsetCoin falseSet value = false then (1 : ℚ)
          else 0) := by
            apply finiteAverage_congr
            intro value
            cases fieldSubsetCoin falseSet value <;> simp
    _ = finiteAverage (fun _value : F ↦ (1 : ℚ)) -
        finiteAverage (fun value : F ↦
          if fieldSubsetCoin falseSet value = false then (1 : ℚ)
          else 0) := by
      unfold finiteAverage
      rw [Finset.sum_sub_distrib]
      ring
    _ = 1 - fieldSubsetFalseMass falseSet := by
      rw [finiteAverage_one, finiteAverage_fieldSubsetCoin_false]

/-- Uniform averaging of an independent finite product factorizes. -/
theorem finiteAverage_pi_prod
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Value] [Nonempty Value]
    (weight : Index → Value → ℚ) :
    finiteAverage (fun sample : Index → Value ↦
      ∏ index, weight index (sample index)) =
      ∏ index, finiteAverage (weight index) := by
  unfold finiteAverage
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_fun]
  rw [Finset.prod_div_distrib]
  simp

private theorem localFieldPatternIndicator_eq_prod
    {coordinates : Nat} {F : Type*} [DecidableEq F]
    (falseSet : Finset F)
    (support : Finset (Fin coordinates))
    (pattern : LocalAssignment support)
    (values : support → F) :
    (if (fun coordinate : support ↦
          fieldSubsetCoin falseSet (values coordinate)) = pattern
      then (1 : ℚ) else 0) =
      ∏ coordinate : support,
        if fieldSubsetCoin falseSet (values coordinate) = pattern coordinate
          then (1 : ℚ) else 0 := by
  by_cases hpattern :
      (fun coordinate : support ↦
        fieldSubsetCoin falseSet (values coordinate)) = pattern
  · rw [if_pos hpattern]
    apply Eq.symm
    apply Finset.prod_eq_one
    intro coordinate _
    have hcoordinate := congrFun hpattern coordinate
    simp [hcoordinate]
  · rw [if_neg hpattern]
    apply Eq.symm
    rw [Finset.prod_eq_zero_iff]
    have hexists : ∃ coordinate : support,
        fieldSubsetCoin falseSet (values coordinate) ≠ pattern coordinate := by
      by_contra hnone
      push_neg at hnone
      apply hpattern
      funext coordinate
      exact hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hexists
    refine ⟨coordinate, Finset.mem_univ _, ?_⟩
    simp [hcoordinate]

/-! ## Exact `k`-wise Boolean law over a finite field -/

/-- Evaluate the bounded-degree polynomial and threshold the result by a
fixed false subset of the field. -/
def polynomialSubsetSource
    {F : Type*} [Field F] [DecidableEq F]
    {coordinates : Nat} (nodes : Fin coordinates → F)
    (independence : Nat) (falseSet : Finset F) :
    Polynomial.degreeLT F independence → Fin coordinates → Bool :=
  fun polynomial coordinate ↦
    fieldSubsetCoin falseSet (polynomial.1.eval (nodes coordinate))

/-- Distinct evaluation nodes give the exact product cylinder law on every
set of at most `independence` coordinates. -/
theorem polynomialSubsetSource_isKWisePatternFalseBiased
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {coordinates : Nat} (nodes : Fin coordinates → F)
    (hnodes : Function.Injective nodes)
    (independence : Nat) (falseSet : Finset F) :
    IsKWisePatternFalseBiased independence
      (fieldSubsetFalseMass falseSet)
      (polynomialSubsetSource nodes independence falseSet) := by
  intro support hcard pattern
  let observable : (support → F) → ℚ := fun values ↦
    if (fun coordinate : support ↦
          fieldSubsetCoin falseSet (values coordinate)) = pattern
      then 1 else 0
  calc
    finiteAverage
        (fun polynomial : Polynomial.degreeLT F independence ↦
          localPatternIndicator support pattern
            (polynomialSubsetSource nodes independence falseSet polynomial)) =
      finiteAverage
        (fun polynomial : Polynomial.degreeLT F independence ↦
          observable
            (supportEvaluationLinearMap nodes independence support
              polynomial)) := by
        apply finiteAverage_congr
        intro polynomial
        change
          (if (fun coordinate : support ↦
                fieldSubsetCoin falseSet
                  (polynomial.1.eval (nodes coordinate.1))) = pattern
            then (1 : ℚ) else 0) =
          (if (fun coordinate : support ↦
                fieldSubsetCoin falseSet
                  (polynomial.1.eval (nodes coordinate.1))) = pattern
            then (1 : ℚ) else 0)
        rfl
    _ = finiteAverage observable :=
      finiteAverage_supportEvaluation nodes independence support
        hnodes.injOn hcard observable
    _ = finiteAverage (fun values : support → F ↦
        ∏ coordinate : support,
          if fieldSubsetCoin falseSet (values coordinate) = pattern coordinate
            then (1 : ℚ) else 0) := by
      apply finiteAverage_congr
      intro values
      exact localFieldPatternIndicator_eq_prod
        falseSet support pattern values
    _ = ∏ coordinate : support,
        finiteAverage (fun value : F ↦
          if fieldSubsetCoin falseSet value = pattern coordinate
            then (1 : ℚ) else 0) := by
      exact finiteAverage_pi_prod
        (fun coordinate : support ↦ fun value : F ↦
          if fieldSubsetCoin falseSet value = pattern coordinate
            then (1 : ℚ) else 0)
    _ = localPatternProductMass (fieldSubsetFalseMass falseSet) pattern := by
      unfold localPatternProductMass
      apply Finset.prod_congr rfl
      intro coordinate _
      cases hvalue : pattern coordinate
      · simpa [hvalue] using finiteAverage_fieldSubsetCoin_false falseSet
      · simpa [hvalue] using finiteAverage_fieldSubsetCoin_true falseSet

/-! ## Exact `GF(2^d)` Boolean-tape realization -/

/-- The finite-field instance is made explicit so that its cardinality can
be compared to the Boolean seed cube. -/
instance binaryGaloisFieldFintype (extensionDegree : Nat) :
    Fintype (GaloisField 2 extensionDegree) :=
  Fintype.ofFinite (GaloisField 2 extensionDegree)

instance binaryGaloisFieldDecidableEq (extensionDegree : Nat) :
    DecidableEq (GaloisField 2 extensionDegree) :=
  Classical.decEq (GaloisField 2 extensionDegree)

/-- `GF(2^d)` has exactly `2^d` elements when `d > 0`. -/
theorem binaryGaloisField_card
    (extensionDegree : Nat) (hpositive : extensionDegree ≠ 0) :
    Fintype.card (GaloisField 2 extensionDegree) = 2 ^ extensionDegree := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 extensionDegree hpositive

/-- Choose exactly `falseCount` false field values.  The choice is semantic:
no efficient membership algorithm is asserted. -/
def binaryGaloisFalseSet
    (extensionDegree falseCount : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hcount : falseCount ≤ 2 ^ extensionDegree) :
    Finset (GaloisField 2 extensionDegree) := by
  classical
  have hcard : falseCount ≤
      (Finset.univ : Finset (GaloisField 2 extensionDegree)).card := by
    simpa [binaryGaloisField_card extensionDegree hpositive] using hcount
  exact Classical.choose (Finset.exists_subset_card_eq hcard)

@[simp]
theorem binaryGaloisFalseSet_card
    (extensionDegree falseCount : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hcount : falseCount ≤ 2 ^ extensionDegree) :
    (binaryGaloisFalseSet extensionDegree falseCount hpositive hcount).card =
      falseCount := by
  classical
  unfold binaryGaloisFalseSet
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq (by
      simpa [binaryGaloisField_card extensionDegree hpositive] using hcount))).2

/-- The chosen subset realizes the exact dyadic false mass. -/
theorem binaryGaloisFalseSet_exactMass
    (extensionDegree falseCount : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hcount : falseCount ≤ 2 ^ extensionDegree) :
    fieldSubsetFalseMass
        (binaryGaloisFalseSet extensionDegree falseCount hpositive hcount) =
      (falseCount : ℚ) / (2 : ℚ) ^ extensionDegree := by
  unfold fieldSubsetFalseMass
  rw [binaryGaloisFalseSet_card, binaryGaloisField_card extensionDegree hpositive]
  norm_num

/-- The coefficient cube over `GF(2^d)` is classically equivalent to a flat
Boolean tape of exactly `independence * d` bits.  This is an arbitrary
cardinality equivalence, not a structured coefficient/basis layout, so the
resulting source is not locally decodable.  A future Horner circuit must
introduce such a layout explicitly and transport the finite laws across its
bijection. -/
def binaryPolynomialBitSeedEquiv
    (extensionDegree independence : Nat)
    (hpositive : extensionDegree ≠ 0) :
    (Fin (independence * extensionDegree) → Bool) ≃
      Polynomial.degreeLT (GaloisField 2 extensionDegree) independence := by
  apply Fintype.equivOfCardEq
  rw [card_polynomialDegreeLT,
    binaryGaloisField_card extensionDegree hpositive]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [Nat.mul_comm independence extensionDegree, pow_mul]

/-- Exact seed-cardinality identity, stated independently of the chosen
equivalence. -/
theorem binaryPolynomialSeed_card
    (extensionDegree independence : Nat)
    (hpositive : extensionDegree ≠ 0) :
    Fintype.card
        (Polynomial.degreeLT (GaloisField 2 extensionDegree) independence) =
      2 ^ (independence * extensionDegree) := by
  rw [card_polynomialDegreeLT,
    binaryGaloisField_card extensionDegree hpositive]
  rw [Nat.mul_comm independence extensionDegree, pow_mul]

/-- Boolean-tape version of the finite-field source. -/
def binaryPolynomialBitSource
    {coordinates : Nat}
    (extensionDegree independence falseCount : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hcount : falseCount ≤ 2 ^ extensionDegree)
    (nodes : Fin coordinates → GaloisField 2 extensionDegree) :
    (Fin (independence * extensionDegree) → Bool) →
      Fin coordinates → Bool :=
  fun seed ↦
    polynomialSubsetSource nodes independence
      (binaryGaloisFalseSet extensionDegree falseCount hpositive hcount)
      (binaryPolynomialBitSeedEquiv extensionDegree independence hpositive seed)

/-- The flat `independence * d`-bit source satisfies the exact
`independence`-wise biased product law. -/
theorem binaryPolynomialBitSource_isKWisePatternFalseBiased
    {coordinates : Nat}
    (extensionDegree independence falseCount : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hcount : falseCount ≤ 2 ^ extensionDegree)
    (nodes : Fin coordinates → GaloisField 2 extensionDegree)
    (hnodes : Function.Injective nodes) :
    IsKWisePatternFalseBiased independence
      ((falseCount : ℚ) / (2 : ℚ) ^ extensionDegree)
      (binaryPolynomialBitSource extensionDegree independence falseCount
        hpositive hcount nodes) := by
  intro support hcard pattern
  let seedEquiv :=
    binaryPolynomialBitSeedEquiv extensionDegree independence hpositive
  let falseSet :=
    binaryGaloisFalseSet extensionDegree falseCount hpositive hcount
  calc
    finiteAverage
        (fun seed : Fin (independence * extensionDegree) → Bool ↦
          localPatternIndicator support pattern
            (binaryPolynomialBitSource extensionDegree independence falseCount
              hpositive hcount nodes seed)) =
      finiteAverage
        (fun polynomial :
            Polynomial.degreeLT (GaloisField 2 extensionDegree) independence ↦
          localPatternIndicator support pattern
            (polynomialSubsetSource nodes independence falseSet polynomial)) := by
        simpa [seedEquiv, falseSet, binaryPolynomialBitSource] using
          (finiteAverage_comp_equiv seedEquiv
            (fun polynomial :
                Polynomial.degreeLT
                  (GaloisField 2 extensionDegree) independence ↦
              localPatternIndicator support pattern
                (polynomialSubsetSource nodes independence falseSet polynomial)))
    _ = localPatternProductMass (fieldSubsetFalseMass falseSet) pattern :=
      polynomialSubsetSource_isKWisePatternFalseBiased
        nodes hnodes independence falseSet support hcard pattern
    _ = localPatternProductMass
        ((falseCount : ℚ) / (2 : ℚ) ^ extensionDegree) pattern := by
      rw [binaryGaloisFalseSet_exactMass]

/-! ## Unbiased half-field specialization -/

/-- Product Bernoulli mass at false probability `1/2` is the uniform
cylinder mass. -/
theorem localPatternProductMass_half
    {coordinates : Nat} {support : Finset (Fin coordinates)}
    (pattern : LocalAssignment support) :
    localPatternProductMass ((1 : ℚ) / 2) pattern =
      1 / (2 : ℚ) ^ support.card := by
  unfold localPatternProductMass
  have hterm : ∀ coordinate : support,
      (if pattern coordinate then 1 - (1 : ℚ) / 2 else (1 : ℚ) / 2) =
        (1 : ℚ) / 2 := by
    intro coordinate
    cases pattern coordinate <;> norm_num
  simp_rw [hterm]
  simp [one_div]

/-- For positive `d`, a subset of size `2^(d-1)` occupies exactly half of
`GF(2^d)`. -/
theorem binaryHalfFalseMass
    (extensionDegree : Nat) (hpositive : 0 < extensionDegree) :
    (((2 ^ (extensionDegree - 1) : Nat) : ℚ) /
        (2 : ℚ) ^ extensionDegree) =
      (1 : ℚ) / 2 := by
  obtain ⟨rest, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  simp only [Nat.succ_sub_one, pow_succ, Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (2 : ℚ) ^ rest ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow]

/-- The half-field Boolean-tape source is exactly
`independence`-wise unbiased. -/
theorem binaryHalfPolynomialBitSource_isKWisePatternUnbiased
    {coordinates : Nat}
    (extensionDegree independence : Nat)
    (hpositive : 0 < extensionDegree)
    (nodes : Fin coordinates → GaloisField 2 extensionDegree)
    (hnodes : Function.Injective nodes) :
    IsKWisePatternUnbiased independence
      (binaryPolynomialBitSource extensionDegree independence
        (2 ^ (extensionDegree - 1)) (Nat.ne_of_gt hpositive)
        (by
          exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
            (by omega : extensionDegree - 1 ≤ extensionDegree))
        nodes) := by
  intro support hcard pattern
  have hbiased :=
    binaryPolynomialBitSource_isKWisePatternFalseBiased
      extensionDegree independence (2 ^ (extensionDegree - 1))
      (Nat.ne_of_gt hpositive)
      (by
        exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
          (by omega : extensionDegree - 1 ≤ extensionDegree))
      nodes hnodes support hcard pattern
  rw [binaryHalfFalseMass extensionDegree hpositive] at hbiased
  rw [hbiased]
  exact localPatternProductMass_half pattern

/-! ## Canonical truth-table coordinate nodes -/

/-- When `inputBits ≤ extensionDegree`, choose an embedding of all
`2^inputBits` truth-table coordinates into `GF(2^extensionDegree)`. -/
def binaryTruthTableNodeEmbedding
    (inputBits extensionDegree : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hdegree : inputBits ≤ extensionDegree) :
    Fin (2 ^ inputBits) ↪ GaloisField 2 extensionDegree := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa [binaryGaloisField_card extensionDegree hpositive] using
    (Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hdegree)

theorem binaryTruthTableNodeEmbedding_injective
    (inputBits extensionDegree : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hdegree : inputBits ≤ extensionDegree) :
    Function.Injective
      (binaryTruthTableNodeEmbedding inputBits extensionDegree
        hpositive hdegree) :=
  (binaryTruthTableNodeEmbedding inputBits extensionDegree
    hpositive hdegree).injective

/-- The finite-field source specialized to all truth-table coordinates. -/
def binaryTruthTablePolynomialBitSource
    (inputBits extensionDegree independence falseCount : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hdegree : inputBits ≤ extensionDegree)
    (hcount : falseCount ≤ 2 ^ extensionDegree) :
    (Fin (independence * extensionDegree) → Bool) →
      Fin (2 ^ inputBits) → Bool :=
  binaryPolynomialBitSource extensionDegree independence falseCount
    hpositive hcount
    (binaryTruthTableNodeEmbedding inputBits extensionDegree
      hpositive hdegree)

/-- Exact biased law on the truth-table coordinate set. -/
theorem binaryTruthTablePolynomialBitSource_patternFalseBiased
    (inputBits extensionDegree independence falseCount : Nat)
    (hpositive : extensionDegree ≠ 0)
    (hdegree : inputBits ≤ extensionDegree)
    (hcount : falseCount ≤ 2 ^ extensionDegree) :
    IsKWisePatternFalseBiased independence
      ((falseCount : ℚ) / (2 : ℚ) ^ extensionDegree)
      (binaryTruthTablePolynomialBitSource inputBits extensionDegree
        independence falseCount hpositive hdegree hcount) := by
  exact binaryPolynomialBitSource_isKWisePatternFalseBiased
    extensionDegree independence falseCount hpositive hcount
    (binaryTruthTableNodeEmbedding inputBits extensionDegree
      hpositive hdegree)
    (binaryTruthTableNodeEmbedding_injective inputBits extensionDegree
      hpositive hdegree)

/-- Exact unbiased law on the truth-table coordinate set. -/
theorem binaryTruthTableHalfPolynomialBitSource_patternUnbiased
    (inputBits extensionDegree independence : Nat)
    (hpositive : 0 < extensionDegree)
    (hdegree : inputBits ≤ extensionDegree) :
    IsKWisePatternUnbiased independence
      (binaryTruthTablePolynomialBitSource inputBits extensionDegree
        independence (2 ^ (extensionDegree - 1))
        (Nat.ne_of_gt hpositive) hdegree
        (by
          exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
            (by omega : extensionDegree - 1 ≤ extensionDegree))) := by
  exact binaryHalfPolynomialBitSource_isKWisePatternUnbiased
    extensionDegree independence hpositive
    (binaryTruthTableNodeEmbedding inputBits extensionDegree
      (Nat.ne_of_gt hpositive) hdegree)
    (binaryTruthTableNodeEmbedding_injective inputBits extensionDegree
      (Nat.ne_of_gt hpositive) hdegree)

/-- Exact lower probability package needed for the DPTW `A/B` pair.  It
reduces the two seed lengths from the product-source baseline
`2^inputBits * extensionDegree` to respectively
`4*m*extensionDegree` and `2*m*extensionDegree`.  No coordinate-circuit
bound is part of this theorem. -/
theorem binaryTruthTableDPTWPair_exactLaws
    (inputBits extensionDegree falseCount m : Nat)
    (hpositive : 0 < extensionDegree)
    (hdegree : inputBits ≤ extensionDegree)
    (hcount : falseCount ≤ 2 ^ extensionDegree) :
    IsKWisePatternUnbiased (4 * m)
        (binaryTruthTablePolynomialBitSource inputBits extensionDegree
          (4 * m) (2 ^ (extensionDegree - 1))
          (Nat.ne_of_gt hpositive) hdegree
          (by
            exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
              (by omega : extensionDegree - 1 ≤ extensionDegree))) ∧
      IsKWisePatternFalseBiased (2 * m)
        ((falseCount : ℚ) / (2 : ℚ) ^ extensionDegree)
        (binaryTruthTablePolynomialBitSource inputBits extensionDegree
          (2 * m) falseCount (Nat.ne_of_gt hpositive) hdegree hcount) := by
  constructor
  · exact binaryTruthTableHalfPolynomialBitSource_patternUnbiased
      inputBits extensionDegree (4 * m) hpositive hdegree
  · exact binaryTruthTablePolynomialBitSource_patternFalseBiased
      inputBits extensionDegree (2 * m) falseCount
      (Nat.ne_of_gt hpositive) hdegree hcount

/-! ## Exact inverse-power tail parameter -/

/-- Choosing exactly `2^(extensionDegree-tailBits)` false field values gives
false mass exactly `2^(-tailBits)`.  Thus no probability rounding is needed
for inverse powers of two when `tailBits ≤ extensionDegree`. -/
theorem binaryDyadicTailFalseMass
    (extensionDegree tailBits : Nat)
    (htail : tailBits ≤ extensionDegree) :
    (((2 ^ (extensionDegree - tailBits) : Nat) : ℚ) /
        (2 : ℚ) ^ extensionDegree) =
      1 / (2 : ℚ) ^ tailBits := by
  have hsplit : extensionDegree - tailBits + tailBits = extensionDegree :=
    Nat.sub_add_cancel htail
  conv_lhs =>
    rhs
    rw [← hsplit, pow_add]
  norm_num [Nat.cast_pow]
  have hleft : (2 : ℚ) ^ (extensionDegree - tailBits) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hright : (2 : ℚ) ^ tailBits ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  field_simp [hleft, hright]

/-- DPTW probability package at the exact parameter
`p = 1 / 2^tailBits`.  The `A` and `B` seeds have respectively
`4*m*extensionDegree` and `2*m*extensionDegree` bits.  This removes dyadic
rounding only at the finite probability layer: the seed equivalence, field
subset, and node embedding remain classically chosen, and no small joint
coordinate circuit is asserted here. -/
theorem binaryTruthTableDPTWDyadicTailPair_exactLaws
    (inputBits extensionDegree tailBits m : Nat)
    (hpositive : 0 < extensionDegree)
    (hdegree : inputBits ≤ extensionDegree)
    (htail : tailBits ≤ extensionDegree) :
    IsKWisePatternUnbiased (4 * m)
        (binaryTruthTablePolynomialBitSource inputBits extensionDegree
          (4 * m) (2 ^ (extensionDegree - 1))
          (Nat.ne_of_gt hpositive) hdegree
          (by
            exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
              (by omega : extensionDegree - 1 ≤ extensionDegree))) ∧
      IsKWisePatternFalseBiased (2 * m)
        (1 / (2 : ℚ) ^ tailBits)
        (binaryTruthTablePolynomialBitSource inputBits extensionDegree
          (2 * m) (2 ^ (extensionDegree - tailBits))
          (Nat.ne_of_gt hpositive) hdegree
          (by
            exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
              (Nat.sub_le extensionDegree tailBits))) := by
  have hlaws := binaryTruthTableDPTWPair_exactLaws
    inputBits extensionDegree (2 ^ (extensionDegree - tailBits)) m
    hpositive hdegree
    (by
      exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
        (Nat.sub_le extensionDegree tailBits))
  rw [binaryDyadicTailFalseMass extensionDegree tailBits htail] at hlaws
  exact hlaws

end DPTWFiniteFieldKWiseSeed

end

end OneTapeMagnification
end Frontier
end Pnp4
