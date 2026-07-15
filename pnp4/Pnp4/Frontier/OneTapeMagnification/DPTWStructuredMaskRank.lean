import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Rank of the structured dyadic mask constraints

For a support `U`, survival under the structured dyadic mask says that the
first `tailBits` chosen-basis coordinates of the bounded-degree polynomial
vanish at every point of `U`.  These are homogeneous linear constraints over
`ZMod 2`.  This file packages their constraint map, identifies survival with
its kernel, and proves that a support containing at least `k` points imposes
at least `k * tailBits` independent constraints on a degree-`< k` polynomial.

This is lower-layer selector-pair infrastructure.  It does not by itself
reduce `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open DPTWFiniteFieldKWiseSeed
open GaloisBilinearTensorBridge
open DPTWStructuredFieldCoordinatePrimitive

namespace DPTWStructuredMaskRank

/-- The `ZMod 2`-linear map recording all prefix-coordinate constraints on a
support.  Its kernel is exactly the set of polynomial seeds for which every
point in the support is frozen by the structured dyadic mask. -/
def supportPrefixConstraintMap
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) :
    Polynomial.degreeLT (GaloisField 2 n) k →ₗ[ZMod 2]
      (support → Fin tailBits → ZMod 2) where
  toFun polynomial index selected :=
    gfTwoCoordinates n (Nat.ne_of_gt hn)
      (polynomial.1.eval
        (structuredTruthTableNode n (Nat.ne_of_gt hn) index.1))
      (prefixPosition n tailBits htail selected)
  map_add' left right := by
    funext index selected
    simp
  map_smul' scalar polynomial := by
    funext index selected
    simp

/-- Rank means the binary dimension of the image of the constraint map. -/
def supportPrefixConstraintRank
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) : Nat :=
  Module.finrank (ZMod 2)
    (LinearMap.range
      (supportPrefixConstraintMap n k tailBits hn htail support))

theorem supportPrefixConstraintMap_eq_zero_iff
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n)))
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k) :
    supportPrefixConstraintMap n k tailBits hn htail support polynomial = 0 ↔
      ∀ index : support, ∀ selected : Fin tailBits,
        gfTwoBoolCoordinates n (Nat.ne_of_gt hn)
          (polynomial.1.eval
            (structuredTruthTableNode n (Nat.ne_of_gt hn) index.1))
          (prefixPosition n tailBits htail selected) = false := by
  constructor
  · intro hzero index selected
    have hcoordinate := congrFun (congrFun hzero index) selected
    change
      gfTwoCoordinates n (Nat.ne_of_gt hn)
          (polynomial.1.eval
            (structuredTruthTableNode n (Nat.ne_of_gt hn) index.1))
          (prefixPosition n tailBits htail selected) = 0 at hcoordinate
    rw [gfTwoBoolCoordinates_apply, hcoordinate, zmodTwoEquivBool_zero]
  · intro hfalse
    funext index selected
    change
      gfTwoCoordinates n (Nat.ne_of_gt hn)
          (polynomial.1.eval
            (structuredTruthTableNode n (Nat.ne_of_gt hn) index.1))
          (prefixPosition n tailBits htail selected) = 0
    apply zmodTwoEquivBool.injective
    simpa [gfTwoBoolCoordinates_apply] using hfalse index selected

/-- Kernel membership is pointwise mask survival on the support. -/
theorem supportPrefixConstraintMap_eq_zero_iff_source_false
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n)))
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k) :
    supportPrefixConstraintMap n k tailBits hn htail support polynomial = 0 ↔
      ∀ index ∈ support,
        polynomialSubsetSource
            (structuredTruthTableNode n (Nat.ne_of_gt hn)) k
            (zeroPrefixFalseSet n tailBits (Nat.ne_of_gt hn) htail)
            polynomial index = false := by
  rw [supportPrefixConstraintMap_eq_zero_iff]
  constructor
  · intro hfalse index hindex
    rw [polynomialSubsetSource, fieldSubsetCoin_eq_false_iff,
      mem_zeroPrefixFalseSet]
    exact hfalse ⟨index, hindex⟩
  · intro hsource index selected
    have hfalse := hsource index.1 index.2
    rw [polynomialSubsetSource, fieldSubsetCoin_eq_false_iff,
      mem_zeroPrefixFalseSet] at hfalse
    exact hfalse selected

/-- The pointwise survival indicator is the characteristic function of the
constraint kernel. -/
theorem maskAllZeroIndicator_polynomialSubsetSource_eq_kernelIndicator
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n)))
    (polynomial : Polynomial.degreeLT (GaloisField 2 n) k) :
    maskAllZeroIndicator support
        (polynomialSubsetSource
          (structuredTruthTableNode n (Nat.ne_of_gt hn)) k
          (zeroPrefixFalseSet n tailBits (Nat.ne_of_gt hn) htail)
          polynomial) =
      if supportPrefixConstraintMap n k tailBits hn htail support polynomial = 0
      then 1 else 0 := by
  unfold maskAllZeroIndicator
  by_cases hzero :
      supportPrefixConstraintMap n k tailBits hn htail support polynomial = 0
  · rw [if_pos hzero, if_pos]
    exact (supportPrefixConstraintMap_eq_zero_iff_source_false
      n k tailBits hn htail support polynomial).mp hzero
  · rw [if_neg hzero, if_neg]
    intro hsource
    exact hzero ((supportPrefixConstraintMap_eq_zero_iff_source_false
      n k tailBits hn htail support polynomial).mpr hsource)

/-- Uniform averaging of a kernel indicator counts exactly the kernel. -/
theorem finiteAverage_linearMap_kernelIndicator_eq_card
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    [Fintype V] [Fintype W] [DecidableEq W]
    (map : V →ₗ[ZMod 2] W) :
    finiteAverage (fun value : V ↦
      if map value = 0 then (1 : Rat) else 0) =
      (Nat.card (LinearMap.ker map) : Rat) / Fintype.card V := by
  classical
  letI : Fintype (LinearMap.ker map) := Fintype.ofFinite _
  unfold finiteAverage
  congr 1
  rw [Nat.card_eq_fintype_card]
  calc
    (∑ value : V, if map value = 0 then (1 : Rat) else 0) =
        ((Finset.univ.filter (fun value : V ↦ map value = 0)).card : Rat) := by
      simp only [Finset.sum_boole]
    _ = Fintype.card {value : V // map value = 0} := by
      exact_mod_cast
        (Fintype.card_subtype (fun value : V ↦ map value = 0)).symm
    _ = Fintype.card (LinearMap.ker map) := by
      let kernelEquiv : {value : V // map value = 0} ≃ LinearMap.ker map :=
        { toFun := fun value ↦ ⟨value.1, value.2⟩
          invFun := fun value ↦ ⟨value.1, value.2⟩
          left_inv := fun value ↦ by cases value; rfl
          right_inv := fun value ↦ by cases value; rfl }
      exact_mod_cast Fintype.card_congr kernelEquiv

/-- Exact polynomial-space survival probability: kernel cardinality divided
by the total coefficient-space cardinality. -/
theorem finiteAverage_polynomialMaskSurvival_eq_kernelCard
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) :
    finiteAverage (fun polynomial :
        Polynomial.degreeLT (GaloisField 2 n) k ↦
      maskAllZeroIndicator support
        (polynomialSubsetSource
          (structuredTruthTableNode n (Nat.ne_of_gt hn)) k
          (zeroPrefixFalseSet n tailBits (Nat.ne_of_gt hn) htail)
          polynomial)) =
      (Nat.card
          (LinearMap.ker
            (supportPrefixConstraintMap n k tailBits hn htail support)) : Rat) /
        Fintype.card (Polynomial.degreeLT (GaloisField 2 n) k) := by
  calc
    finiteAverage (fun polynomial :
        Polynomial.degreeLT (GaloisField 2 n) k ↦
      maskAllZeroIndicator support
        (polynomialSubsetSource
          (structuredTruthTableNode n (Nat.ne_of_gt hn)) k
          (zeroPrefixFalseSet n tailBits (Nat.ne_of_gt hn) htail)
          polynomial)) =
      finiteAverage (fun polynomial :
          Polynomial.degreeLT (GaloisField 2 n) k ↦
        if supportPrefixConstraintMap n k tailBits hn htail support polynomial = 0
        then 1 else 0) := by
          apply finiteAverage_congr
          intro polynomial
          exact
            maskAllZeroIndicator_polynomialSubsetSource_eq_kernelIndicator
              n k tailBits hn htail support polynomial
    _ = _ := finiteAverage_linearMap_kernelIndicator_eq_card
      (supportPrefixConstraintMap n k tailBits hn htail support)

/-! ## Interpolation gives independent prefix constraints -/

/-- On at most `k` distinct evaluation points, arbitrary prefix-coordinate
targets can be interpolated by a degree-`< k` polynomial. -/
theorem supportPrefixConstraintMap_surjective
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) (hcard : support.card ≤ k) :
    Function.Surjective
      (supportPrefixConstraintMap n k tailBits hn htail support) := by
  classical
  intro target
  let extendedCoordinates : support → Fin n → ZMod 2 :=
    fun index ↦ Function.extend
      (prefixPosition n tailBits htail) (target index) (fun _ ↦ 0)
  let fieldValues : support → GaloisField 2 n :=
    fun index ↦
      (gfTwoCoordinates n (Nat.ne_of_gt hn)).symm
        (extendedCoordinates index)
  obtain ⟨polynomial, hevaluation⟩ :=
    supportEvaluationLinearMap_surjective
      (structuredTruthTableNode n (Nat.ne_of_gt hn)) k support
      (structuredTruthTableNode_injective n (Nat.ne_of_gt hn)).injOn
      hcard fieldValues
  refine ⟨polynomial, ?_⟩
  funext index selected
  have hvalue := congrFun hevaluation index
  change
    polynomial.1.eval
        (structuredTruthTableNode n (Nat.ne_of_gt hn) index.1) =
      fieldValues index at hvalue
  change
    gfTwoCoordinates n (Nat.ne_of_gt hn)
        (polynomial.1.eval
          (structuredTruthTableNode n (Nat.ne_of_gt hn) index.1))
        (prefixPosition n tailBits htail selected) = target index selected
  rw [hvalue]
  change
    gfTwoCoordinates n (Nat.ne_of_gt hn)
        ((gfTwoCoordinates n (Nat.ne_of_gt hn)).symm
          (extendedCoordinates index))
        (prefixPosition n tailBits htail selected) = target index selected
  rw [LinearEquiv.apply_symm_apply]
  exact (prefixPosition_injective n tailBits htail).extend_apply
    (target index) (fun _ ↦ 0) selected

/-- For a small support, the constraint rank is exactly one independent bit
per selected field coordinate and support point. -/
theorem supportPrefixConstraintRank_eq_card_mul
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) (hcard : support.card ≤ k) :
    supportPrefixConstraintRank n k tailBits hn htail support =
      support.card * tailBits := by
  unfold supportPrefixConstraintRank
  rw [LinearMap.range_eq_top.mpr
      (supportPrefixConstraintMap_surjective
        n k tailBits hn htail support hcard),
    finrank_top]
  simp [Module.finrank_pi_fintype]

/-- Restrict a large support's constraint vector to a smaller support. -/
def prefixConstraintRestrictionMap
    (tailBits : Nat)
    {small large : Finset (Fin (2 ^ n))} (hsubset : small ⊆ large) :
    (large → Fin tailBits → ZMod 2) →ₗ[ZMod 2]
      (small → Fin tailBits → ZMod 2) where
  toFun values index := values ⟨index.1, hsubset index.2⟩
  map_add' left right := by rfl
  map_smul' scalar value := by rfl

theorem prefixConstraintRestrictionMap_comp
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    {small large : Finset (Fin (2 ^ n))} (hsubset : small ⊆ large) :
    (prefixConstraintRestrictionMap tailBits hsubset).comp
        (supportPrefixConstraintMap n k tailBits hn htail large) =
      supportPrefixConstraintMap n k tailBits hn htail small := by
  ext polynomial index selected
  rfl

/-- Once the support contains `k` points, the full constraint system has at
least `k * tailBits` independent binary equations. -/
theorem supportPrefixConstraintRank_lowerBound
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) (hcard : k ≤ support.card) :
    k * tailBits ≤
      supportPrefixConstraintRank n k tailBits hn htail support := by
  classical
  obtain ⟨selected, hselectedSubset, hselectedCard⟩ :=
    Finset.exists_subset_card_eq hcard
  let fullMap := supportPrefixConstraintMap
    n k tailBits hn htail support
  let selectedMap := supportPrefixConstraintMap
    n k tailBits hn htail selected
  let restrictMap := prefixConstraintRestrictionMap
    tailBits hselectedSubset
  let rangeToSelected : LinearMap.range fullMap →ₗ[ZMod 2]
      (selected → Fin tailBits → ZMod 2) :=
    restrictMap.comp (LinearMap.range fullMap).subtype
  have hselectedSurjective : Function.Surjective selectedMap :=
    supportPrefixConstraintMap_surjective
      n k tailBits hn htail selected (by omega)
  have hrangeSurjective : Function.Surjective rangeToSelected := by
    intro target
    obtain ⟨polynomial, hpolynomial⟩ := hselectedSurjective target
    let fullValue : LinearMap.range fullMap :=
      ⟨fullMap polynomial, ⟨polynomial, rfl⟩⟩
    refine ⟨fullValue, ?_⟩
    change restrictMap (fullMap polynomial) = target
    have hcomp := congrArg (fun map ↦ map polynomial)
      (prefixConstraintRestrictionMap_comp
        n k tailBits hn htail hselectedSubset)
    change restrictMap (fullMap polynomial) = selectedMap polynomial at hcomp
    rw [hcomp, hpolynomial]
  have hdimension := rangeToSelected.finrank_range_le
  rw [LinearMap.range_eq_top.mpr hrangeSurjective,
    finrank_top] at hdimension
  change
    Module.finrank (ZMod 2)
        (selected → Fin tailBits → ZMod 2) ≤
      supportPrefixConstraintRank n k tailBits hn htail support at hdimension
  simpa [Module.finrank_pi_fintype,
    hselectedCard] using hdimension

/-! ## Exact rank formula and the actual structured mask -/

/-- Rank-nullity converts the kernel-card ratio into the exact dyadic
probability `2^(-rank)`. -/
theorem kernelCard_div_degreeLTCard_eq_invPowRank
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) :
    (Nat.card
          (LinearMap.ker
            (supportPrefixConstraintMap n k tailBits hn htail support)) : Rat) /
        Fintype.card (Polynomial.degreeLT (GaloisField 2 n) k) =
      1 / (2 : Rat) ^
        supportPrefixConstraintRank n k tailBits hn htail support := by
  let map := supportPrefixConstraintMap n k tailBits hn htail support
  letI : Fintype (LinearMap.ker map) := Fintype.ofFinite _
  have hkernelCard :
      Nat.card (LinearMap.ker map) =
        2 ^ Module.finrank (ZMod 2) (LinearMap.ker map) := by
    calc
      Nat.card (LinearMap.ker map) =
          Fintype.card (LinearMap.ker map) := Nat.card_eq_fintype_card
      _ = Fintype.card (ZMod 2) ^
          Module.finrank (ZMod 2) (LinearMap.ker map) :=
        Module.card_eq_pow_finrank
      _ = _ := by rw [ZMod.card]
  have hdomainCard :
      Fintype.card (Polynomial.degreeLT (GaloisField 2 n) k) =
        2 ^ Module.finrank (ZMod 2)
          (Polynomial.degreeLT (GaloisField 2 n) k) := by
    calc
      Fintype.card (Polynomial.degreeLT (GaloisField 2 n) k) =
          Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2)
            (Polynomial.degreeLT (GaloisField 2 n) k) :=
        Module.card_eq_pow_finrank
      _ = _ := by rw [ZMod.card]
  have hrankNullity := map.finrank_range_add_finrank_ker
  change
    (Nat.card (LinearMap.ker map) : Rat) /
        Fintype.card (Polynomial.degreeLT (GaloisField 2 n) k) =
      1 / (2 : Rat) ^
        Module.finrank (ZMod 2) (LinearMap.range map)
  rw [hkernelCard, hdomainCard, ← hrankNullity]
  push_cast
  rw [pow_add]
  have hnonzero :
      (2 : Rat) ^ Module.finrank (ZMod 2) (LinearMap.ker map) ≠ 0 := by
    positivity
  field_simp
  ring

/-- Exact survival probability for the explicit Boolean coefficient seed of
the actual structured dyadic primitive. -/
theorem structuredDyadicPrimitive_maskSurvival_eq_invPowRank
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) :
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) → Bool ↦
          maskAllZeroIndicator support
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) =
      1 / (2 : Rat) ^
        supportPrefixConstraintRank n (structuredIndependence m) tailBits
          hn htail support := by
  let seedEquiv := structuredPolynomialBitSeedEquiv
    (structuredIndependence m) n (Nat.ne_of_gt hn)
  let observable :
      Polynomial.degreeLT (GaloisField 2 n) (structuredIndependence m) → Rat :=
    fun polynomial ↦
      maskAllZeroIndicator support
        (polynomialSubsetSource
          (structuredTruthTableNode n (Nat.ne_of_gt hn))
          (structuredIndependence m)
          (zeroPrefixFalseSet n tailBits (Nat.ne_of_gt hn) htail)
          polynomial)
  calc
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) → Bool ↦
          maskAllZeroIndicator support
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) =
      finiteAverage (fun seed : Fin (structuredIndependence m * n) → Bool ↦
        observable (seedEquiv seed)) := by
          apply finiteAverage_congr
          intro seed
          rw [structuredDyadicPrimitive_generate]
          rfl
    _ = finiteAverage observable :=
      finiteAverage_comp_equiv seedEquiv observable
    _ =
        (Nat.card
            (LinearMap.ker
              (supportPrefixConstraintMap n (structuredIndependence m)
                tailBits hn htail support)) : Rat) /
          Fintype.card
            (Polynomial.degreeLT (GaloisField 2 n)
              (structuredIndependence m)) := by
        exact finiteAverage_polynomialMaskSurvival_eq_kernelCard
          n (structuredIndependence m) tailBits hn htail support
    _ = _ := kernelCard_div_degreeLTCard_eq_invPowRank
      n (structuredIndependence m) tailBits hn htail support

/-- Concrete union-support suppression used by selector-pair estimates.  As
soon as the union contains the polynomial independence degree, its survival
probability is at most `2^(-(k * tailBits))`. -/
theorem structuredDyadicPrimitive_maskSurvival_le_invPow
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n)))
    (hcard : structuredIndependence m ≤ support.card) :
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) → Bool ↦
          maskAllZeroIndicator support
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) ≤
      1 / (2 : Rat) ^ (structuredIndependence m * tailBits) := by
  rw [structuredDyadicPrimitive_maskSurvival_eq_invPowRank]
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_right₀ (by norm_num)
      (supportPrefixConstraintRank_lowerBound
        n (structuredIndependence m) tailBits hn htail support hcard)

/-- Pair-facing form of the same bound: the mask factor in a selector-pair
moment is evaluated on the union of the two Walsh supports. -/
theorem structuredDyadicPrimitive_pairUnionMaskSurvival_le_invPow
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (left right : Finset (Fin (2 ^ n)))
    (hcard : structuredIndependence m ≤ (left ∪ right).card) :
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) → Bool ↦
          maskAllZeroIndicator (left ∪ right)
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed)) ≤
      1 / (2 : Rat) ^ (structuredIndependence m * tailBits) :=
  structuredDyadicPrimitive_maskSurvival_le_invPow
    n m tailBits hn htail (left ∪ right) hcard

/-! ## Full-coordinate specialization -/

/-- A degree-`< k` polynomial over `GF(2^n)` has exactly `k * n` binary
coefficient dimensions. -/
theorem finrank_polynomialDegreeLT_zmodTwo
    (n k : Nat) (hn : 0 < n) :
    Module.finrank (ZMod 2)
        (Polynomial.degreeLT (GaloisField 2 n) k) = k * n := by
  let coefficientEquiv :=
    LinearEquiv.restrictScalars (ZMod 2)
      (Polynomial.degreeLTEquiv (GaloisField 2 n) k)
  calc
    Module.finrank (ZMod 2)
        (Polynomial.degreeLT (GaloisField 2 n) k) =
      Module.finrank (ZMod 2) (Fin k → GaloisField 2 n) :=
        coefficientEquiv.finrank_eq
    _ = ∑ _index : Fin k,
        Module.finrank (ZMod 2) (GaloisField 2 n) := by
          rw [Module.finrank_pi_fintype]
    _ = k * n := by
      simp [GaloisField.finrank 2 (Nat.ne_of_gt hn)]

/-- No constraint map can have rank larger than its `k * n`-bit polynomial
coefficient domain. -/
theorem supportPrefixConstraintRank_upperBound
    (n k tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (support : Finset (Fin (2 ^ n))) :
    supportPrefixConstraintRank n k tailBits hn htail support ≤ k * n := by
  unfold supportPrefixConstraintRank
  rw [← finrank_polynomialDegreeLT_zmodTwo n k hn]
  exact (supportPrefixConstraintMap n k tailBits hn htail support).finrank_range_le

/-- If all `n` field coordinates are constrained and the support contains at
least `k` points, the rank saturates the entire `k * n`-bit seed space. -/
theorem supportPrefixConstraintRank_fullCoordinates
    (n k : Nat) (hn : 0 < n)
    (support : Finset (Fin (2 ^ n))) (hcard : k ≤ support.card) :
    supportPrefixConstraintRank n k n hn (Nat.le_refl n) support = k * n := by
  apply Nat.le_antisymm
  · exact supportPrefixConstraintRank_upperBound
      n k n hn (Nat.le_refl n) support
  · exact supportPrefixConstraintRank_lowerBound
      n k n hn (Nat.le_refl n) support hcard

/-- With a full-coordinate zero mask, `k` interpolation points determine the
whole polynomial.  Hence every support of size at least `k` survives with
the exact probability `(2^(-n))^k`, not merely an upper bound. -/
theorem structuredDyadicPrimitive_fullMaskSurvival_exact
    (n m : Nat) (hn : 0 < n)
    (support : Finset (Fin (2 ^ n)))
    (hcard : structuredIndependence m ≤ support.card) :
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) → Bool ↦
          maskAllZeroIndicator support
            ((structuredDyadicPrimitive n m n hn (Nat.le_refl n)).generate
              seed)) =
      (1 / (2 : Rat) ^ n) ^ structuredIndependence m := by
  rw [structuredDyadicPrimitive_maskSurvival_eq_invPowRank,
    supportPrefixConstraintRank_fullCoordinates
      n (structuredIndependence m) hn support hcard]
  rw [Nat.mul_comm, pow_mul]
  simp [one_div]

/-- Full-coordinate exact specialization in the pair-facing union form. -/
theorem structuredDyadicPrimitive_pairUnionFullMaskSurvival_exact
    (n m : Nat) (hn : 0 < n)
    (left right : Finset (Fin (2 ^ n)))
    (hcard : structuredIndependence m ≤ (left ∪ right).card) :
    finiteAverage
        (fun seed : Fin (structuredIndependence m * n) → Bool ↦
          maskAllZeroIndicator (left ∪ right)
            ((structuredDyadicPrimitive n m n hn (Nat.le_refl n)).generate
              seed)) =
      (1 / (2 : Rat) ^ n) ^ structuredIndependence m :=
  structuredDyadicPrimitive_fullMaskSurvival_exact
    n m hn (left ∪ right) hcard

end DPTWStructuredMaskRank
end
end OneTapeMagnification
end Frontier
end Pnp4
