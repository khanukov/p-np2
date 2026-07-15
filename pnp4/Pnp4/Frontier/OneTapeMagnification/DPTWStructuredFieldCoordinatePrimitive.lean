import Pnp4.Frontier.OneTapeMagnification.DPTWFiniteFieldKWiseSeed
import Pnp4.Frontier.OneTapeMagnification.GaloisBilinearTensorBridge
import Pnp4.Frontier.OneTapeMagnification.DPTWBilinearCoordinateCircuitProbe

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Structured finite-field coordinate primitives

This module joins the exact finite-field law to the polynomial-size Horner
circuit.  In contrast to the cardinality-only equivalence in
`DPTWFiniteFieldKWiseSeed`, every coefficient is represented by its own
contiguous logical block (up to the explicit `finProdFinEquiv` reindexing),
and every field element is decoded through the same chosen `GF(2)` basis used
by the multiplication tensor.

The basis and its multiplication tensor are nonuniform classical advice.  The
result is lower-layer infrastructure: it does not reduce
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`.
-/

noncomputable section

open scoped BigOperators

open Pnp3.ComplexityInterfaces
open StreamingMagnification
open StreamingMagnification.TotalSearch
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open DPTWFiniteBooleanPrimitives
open DPTWFiniteFieldKWiseSeed
open GaloisBilinearTensorBridge
open DPTWBilinearCoordinateCircuitProbe

namespace DPTWStructuredFieldCoordinatePrimitive

/-! ## Coefficient-major Boolean seed layout -/

/-- Reindex a flat `k*d`-bit tape as `k` Boolean vectors of length `d`.
This is the exact layout read by `polynomialHornerBundle`. -/
def flatCoefficientBitsEquiv (k d : Nat) :
    (Fin (k * d) -> Bool) ≃ (Fin k -> Fin d -> Bool) where
  toFun seed coefficient bit := seed (finProdFinEquiv (coefficient, bit))
  invFun blocks index :=
    blocks (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2
  left_inv seed := by
    funext index
    exact congrArg seed (finProdFinEquiv.apply_symm_apply index)
  right_inv blocks := by
    funext coefficient bit
    simp

@[simp]
theorem flatCoefficientBitsEquiv_apply
    (k d : Nat) (seed : Fin (k * d) -> Bool)
    (coefficient : Fin k) (bit : Fin d) :
    flatCoefficientBitsEquiv k d seed coefficient bit =
      seed (finProdFinEquiv (coefficient, bit)) :=
  rfl

/-- Decode each coefficient block independently through the chosen basis. -/
def coefficientFieldEquiv (k d : Nat) (hd : d ≠ 0) :
    (Fin k -> Fin d -> Bool) ≃ (Fin k -> GaloisField 2 d) where
  toFun blocks coefficient :=
    (gfTwoBoolCoordinates d hd).symm (blocks coefficient)
  invFun coefficients coefficient :=
    gfTwoBoolCoordinates d hd (coefficients coefficient)
  left_inv blocks := by
    funext coefficient bit
    exact congrFun
      ((gfTwoBoolCoordinates d hd).apply_symm_apply (blocks coefficient)) bit
  right_inv coefficients := by
    funext coefficient
    simp

/-- The structured seed equivalence: flat bits, coefficient blocks, basis
decoding, and finally the standard bounded-degree coefficient equivalence.
No arbitrary `Fintype.equivOfCardEq` occurs in this definition. -/
def structuredPolynomialBitSeedEquiv (k d : Nat) (hd : d ≠ 0) :
    (Fin (k * d) -> Bool) ≃
      Polynomial.degreeLT (GaloisField 2 d) k :=
  (flatCoefficientBitsEquiv k d).trans
    ((coefficientFieldEquiv k d hd).trans
      (Polynomial.degreeLTEquiv (GaloisField 2 d) k).symm.toEquiv)

@[simp]
theorem structuredPolynomialBitSeedEquiv_coefficient
    (k d : Nat) (hd : d ≠ 0)
    (seed : Fin (k * d) -> Bool) (coefficient : Fin k) :
    Polynomial.degreeLTEquiv (GaloisField 2 d) k
        (structuredPolynomialBitSeedEquiv k d hd seed) coefficient =
      (gfTwoBoolCoordinates d hd).symm
        (fun bit => seed (finProdFinEquiv (coefficient, bit))) := by
  change
    (Polynomial.degreeLTEquiv (GaloisField 2 d) k)
      ((Polynomial.degreeLTEquiv (GaloisField 2 d) k).symm
        (fun coefficient =>
          (gfTwoBoolCoordinates d hd).symm
            (fun bit => seed (finProdFinEquiv (coefficient, bit)))))
        coefficient = _
  rw [LinearEquiv.apply_symm_apply]

/-! ## Structured truth-table nodes and exact product law -/

/-- Decode the canonical `d`-bit truth-table input in the same field basis. -/
def structuredTruthTableNode (d : Nat) (hd : d ≠ 0)
    (index : Fin (2 ^ d)) : GaloisField 2 d :=
  (gfTwoBoolCoordinates d hd).symm (lexInput d index)

theorem structuredTruthTableNode_injective (d : Nat) (hd : d ≠ 0) :
    Function.Injective (structuredTruthTableNode d hd) := by
  intro left right hequal
  have hbits : lexInput d left = lexInput d right :=
    (gfTwoBoolCoordinates d hd).symm.injective hequal
  have hrank := congrArg StreamingMagnification.FixedBitstringCodec.rank hbits
  simpa using hrank

/-- Thresholded polynomial evaluation using the structured coefficient tape. -/
def structuredPolynomialSubsetSource
    (d k : Nat) (hd : d ≠ 0)
    (falseSet : Finset (GaloisField 2 d)) :
    (Fin (k * d) -> Bool) -> Fin (2 ^ d) -> Bool :=
  fun seed =>
    polynomialSubsetSource (structuredTruthTableNode d hd) k falseSet
      (structuredPolynomialBitSeedEquiv k d hd seed)

/-- Transporting the polynomial law through the explicit structured
equivalence preserves the exact `k`-wise product cylinders. -/
theorem structuredPolynomialSubsetSource_isKWisePatternFalseBiased
    (d k : Nat) (hd : d ≠ 0)
    (falseSet : Finset (GaloisField 2 d)) :
    IsKWisePatternFalseBiased k (fieldSubsetFalseMass falseSet)
      (structuredPolynomialSubsetSource d k hd falseSet) := by
  intro support hcard pattern
  let seedEquiv := structuredPolynomialBitSeedEquiv k d hd
  calc
    finiteAverage (fun seed : Fin (k * d) -> Bool =>
        localPatternIndicator support pattern
          (structuredPolynomialSubsetSource d k hd falseSet seed)) =
      finiteAverage (fun polynomial :
          Polynomial.degreeLT (GaloisField 2 d) k =>
        localPatternIndicator support pattern
          (polynomialSubsetSource (structuredTruthTableNode d hd) k
            falseSet polynomial)) := by
      simpa [seedEquiv, structuredPolynomialSubsetSource] using
        (DPTWFiniteFieldKWiseSeed.finiteAverage_comp_equiv seedEquiv
          (fun polynomial : Polynomial.degreeLT (GaloisField 2 d) k =>
            localPatternIndicator support pattern
              (polynomialSubsetSource (structuredTruthTableNode d hd) k
                falseSet polynomial)))
    _ = localPatternProductMass (fieldSubsetFalseMass falseSet) pattern :=
      polynomialSubsetSource_isKWisePatternFalseBiased
        (structuredTruthTableNode d hd)
        (structuredTruthTableNode_injective d hd) k falseSet
        support hcard pattern

/-! ## The canonical zero-prefix false set -/

/-- The canonical injection of the first `t` coordinate positions into a
`d`-bit field representation. -/
def prefixPosition (d t : Nat) (ht : t ≤ d) (index : Fin t) : Fin d :=
  Fin.castLE ht index

theorem prefixPosition_injective (d t : Nat) (ht : t ≤ d) :
    Function.Injective (prefixPosition d t ht) := by
  intro left right hequal
  apply Fin.ext
  exact congrArg (fun index : Fin d => index.val) hequal

/-- Merge a fixed all-zero prefix and an arbitrary suffix. -/
def zeroPrefixBits (d t : Nat) (ht : t ≤ d)
    (suffix : Fin (d - t) -> Bool) : Fin d -> Bool :=
  fun index =>
    Fin.addCases (fun _prefix => false) suffix
      (Fin.cast (Nat.add_sub_of_le ht).symm index)

@[simp]
theorem zeroPrefixBits_prefix
    (d t : Nat) (ht : t ≤ d) (suffix : Fin (d - t) -> Bool)
    (index : Fin t) :
    zeroPrefixBits d t ht suffix (prefixPosition d t ht index) = false := by
  unfold zeroPrefixBits prefixPosition
  have hindex :
      Fin.cast (Nat.add_sub_of_le ht).symm (Fin.castLE ht index) =
        Fin.castAdd (d - t) index := by
    apply Fin.ext
    rfl
  rw [hindex, Fin.addCases_left]

/-- Position of a free suffix coordinate in the full `d`-bit vector. -/
def suffixPosition (d t : Nat) (ht : t ≤ d)
    (index : Fin (d - t)) : Fin d :=
  Fin.cast (Nat.add_sub_of_le ht) (Fin.natAdd t index)

@[simp]
theorem zeroPrefixBits_suffix
    (d t : Nat) (ht : t ≤ d) (suffix : Fin (d - t) -> Bool)
    (index : Fin (d - t)) :
    zeroPrefixBits d t ht suffix (suffixPosition d t ht index) =
      suffix index := by
  unfold zeroPrefixBits suffixPosition
  have hindex :
      Fin.cast (Nat.add_sub_of_le ht).symm
          (Fin.cast (Nat.add_sub_of_le ht) (Fin.natAdd t index)) =
        Fin.natAdd t index := by
    apply Fin.ext
    rfl
  rw [hindex, Fin.addCases_right]

/-- Free suffix bits are equivalent to full bit vectors whose first `t`
positions are all zero. -/
def zeroPrefixBitsEquiv (d t : Nat) (ht : t ≤ d) :
    (Fin (d - t) -> Bool) ≃
      {bits : Fin d -> Bool //
        forall index : Fin t, bits (prefixPosition d t ht index) = false} where
  toFun suffix :=
    ⟨zeroPrefixBits d t ht suffix,
      zeroPrefixBits_prefix d t ht suffix⟩
  invFun bits index := bits.1 (suffixPosition d t ht index)
  left_inv suffix := by
    funext index
    exact zeroPrefixBits_suffix d t ht suffix index
  right_inv bits := by
    apply Subtype.ext
    funext index
    let split : Fin (t + (d - t)) :=
      Fin.cast (Nat.add_sub_of_le ht).symm index
    have hindex : Fin.cast (Nat.add_sub_of_le ht) split = index := by
      apply Fin.ext
      rfl
    rw [← hindex]
    refine Fin.addCases
      (motive := fun splitIndex =>
        zeroPrefixBits d t ht
            (fun suffix => bits.1 (suffixPosition d t ht suffix))
            (Fin.cast (Nat.add_sub_of_le ht) splitIndex) =
          bits.1 (Fin.cast (Nat.add_sub_of_le ht) splitIndex))
      (fun prefixIndex => ?_)
      (fun suffixIndex => ?_)
      split
    · dsimp only
      have hposition :
          Fin.cast (Nat.add_sub_of_le ht)
              (Fin.castAdd (d - t) prefixIndex) =
            prefixPosition d t ht prefixIndex := by
        apply Fin.ext
        rfl
      rw [hposition, zeroPrefixBits_prefix]
      exact (bits.property prefixIndex).symm
    · dsimp only
      change
        zeroPrefixBits d t ht
            (fun suffix => bits.1 (suffixPosition d t ht suffix))
            (suffixPosition d t ht suffixIndex) =
          bits.1 (suffixPosition d t ht suffixIndex)
      rw [zeroPrefixBits_suffix]

/-- Field elements whose first `t` chosen-basis coordinates are zero. -/
def zeroPrefixFalseSet (d t : Nat) (hd : d ≠ 0) (ht : t ≤ d) :
    Finset (GaloisField 2 d) := by
  classical
  exact Finset.univ.filter (fun value =>
    forall index : Fin t,
      gfTwoBoolCoordinates d hd value (prefixPosition d t ht index) = false)

@[simp]
theorem mem_zeroPrefixFalseSet
    (d t : Nat) (hd : d ≠ 0) (ht : t ≤ d)
    (value : GaloisField 2 d) :
    value ∈ zeroPrefixFalseSet d t hd ht ↔
      forall index : Fin t,
        gfTwoBoolCoordinates d hd value (prefixPosition d t ht index) = false := by
  classical
  simp [zeroPrefixFalseSet]

/-- The coordinate equivalence restricts to an equivalence between the
zero-prefix Boolean subtype and the zero-prefix field subtype. -/
def zeroPrefixBitsFieldSubtypeEquiv
    (d t : Nat) (hd : d ≠ 0) (ht : t ≤ d) :
    {bits : Fin d -> Bool //
        forall index : Fin t, bits (prefixPosition d t ht index) = false} ≃
      {value : GaloisField 2 d //
        forall index : Fin t,
          gfTwoBoolCoordinates d hd value
            (prefixPosition d t ht index) = false} :=
  Equiv.subtypeEquiv (gfTwoBoolCoordinates d hd).symm (fun bits => by
    constructor
    · intro h index
      have hcoordinate := congrFun
        ((gfTwoBoolCoordinates d hd).apply_symm_apply bits)
        (prefixPosition d t ht index)
      rw [hcoordinate]
      exact h index
    · intro h index
      have hi := h index
      have hcoordinate := congrFun
        ((gfTwoBoolCoordinates d hd).apply_symm_apply bits)
        (prefixPosition d t ht index)
      rw [hcoordinate] at hi
      exact hi)

/-- The zero-prefix field subtype has one free Boolean choice per suffix
coordinate. -/
def zeroPrefixFieldSubtypeEquiv
    (d t : Nat) (hd : d ≠ 0) (ht : t ≤ d) :
    (Fin (d - t) -> Bool) ≃
      {value : GaloisField 2 d //
        forall index : Fin t,
          gfTwoBoolCoordinates d hd value
            (prefixPosition d t ht index) = false} :=
  (zeroPrefixBitsEquiv d t ht).trans
    (zeroPrefixBitsFieldSubtypeEquiv d t hd ht)

/-- The canonical prefix-zero set has exactly `2^(d-t)` elements. -/
theorem zeroPrefixFalseSet_card
    (d t : Nat) (hd : d ≠ 0) (ht : t ≤ d) :
    (zeroPrefixFalseSet d t hd ht).card = 2 ^ (d - t) := by
  classical
  let predicateSubtype :=
    {value : GaloisField 2 d //
      forall index : Fin t,
        gfTwoBoolCoordinates d hd value
          (prefixPosition d t ht index) = false}
  let membershipSubtype :=
    {value : GaloisField 2 d // value ∈ zeroPrefixFalseSet d t hd ht}
  let membershipEquiv : predicateSubtype ≃ membershipSubtype :=
    Equiv.subtypeEquiv (Equiv.refl (GaloisField 2 d)) (fun value => by
      exact (mem_zeroPrefixFalseSet d t hd ht value).symm)
  have hfree :
      Fintype.card (Fin (d - t) -> Bool) = 2 ^ (d - t) := by
    simp
  have hpredicate : Fintype.card predicateSubtype = 2 ^ (d - t) := by
    rw [← hfree]
    exact Fintype.card_congr (zeroPrefixFieldSubtypeEquiv d t hd ht).symm
  have hmembership : Fintype.card membershipSubtype = 2 ^ (d - t) := by
    rw [← hpredicate]
    exact Fintype.card_congr membershipEquiv.symm
  rw [← Fintype.card_coe]
  exact hmembership

/-- Consequently the exact false mass is `2^-t`. -/
theorem zeroPrefixFalseSet_exactMass
    (d t : Nat) (hd : d ≠ 0) (ht : t ≤ d) :
    fieldSubsetFalseMass (zeroPrefixFalseSet d t hd ht) =
      1 / (2 : Rat) ^ t := by
  unfold fieldSubsetFalseMass
  rw [zeroPrefixFalseSet_card d t hd ht,
    binaryGaloisField_card d hd]
  simpa [Nat.cast_pow] using binaryDyadicTailFalseMass d t ht

/-! ## Boolean tensor semantics -/

/-- The recursive circuit parity fold is the `ZMod 2` sum of the same finite
Boolean family. -/
theorem xorFamilyValue_eq_boolXorSum :
    forall (count : Nat) (family : Fin count -> Bool),
      xorFamilyValue count family = boolXorSum family
  | 0, family => by
      simp [xorFamilyValue, boolXorSum]
  | count + 1, family => by
      rw [xorFamilyValue]
      have hcast :
          (fun index : Fin count => family (Fin.castAdd 1 index)) =
            (fun index : Fin count => family index.castSucc) := by
        funext index
        congr 1
      rw [hcast, xorFamilyValue_eq_boolXorSum]
      unfold boolXorSum
      rw [Fin.sum_univ_castSucc, zmodTwoEquivBool_add]
      have hlast : Fin.natAdd count (0 : Fin 1) = Fin.last count := by
        apply Fin.ext
        rfl
      rw [hlast]
      simp

/-- Flattening a rectangular tensor with `finProdFinEquiv` preserves its
iterated Boolean XOR. -/
theorem xorFamilyValue_finProd_eq_boolXorSum₂
    (d : Nat) (family : Fin d -> Fin d -> Bool) :
    xorFamilyValue (d * d) (fun term =>
      let pair := finProdFinEquiv.symm term
      family pair.1 pair.2) =
      boolXorSum₂ family := by
  rw [xorFamilyValue_eq_boolXorSum]
  unfold boolXorSum₂ boolXorSum
  apply congrArg zmodTwoEquivBool
  simp only [Equiv.symm_apply_apply]
  calc
    (∑ term : Fin (d * d),
        zmodTwoEquivBool.symm
          (family (finProdFinEquiv.symm term).1
            (finProdFinEquiv.symm term).2)) =
      ∑ pair : Fin d × Fin d,
        zmodTwoEquivBool.symm (family pair.1 pair.2) := by
      symm
      exact Fintype.sum_equiv finProdFinEquiv
        (fun pair : Fin d × Fin d =>
          zmodTwoEquivBool.symm (family pair.1 pair.2))
        (fun term : Fin (d * d) =>
          zmodTwoEquivBool.symm
            (family (finProdFinEquiv.symm term).1
              (finProdFinEquiv.symm term).2))
        (fun pair => by simp)
    _ = ∑ i : Fin d, ∑ j : Fin d,
        zmodTwoEquivBool.symm (family i j) :=
      Fintype.sum_prod_type
        (fun pair : Fin d × Fin d =>
          zmodTwoEquivBool.symm (family pair.1 pair.2))

/-- The circuit tensor instantiated from the chosen field basis computes
exactly field multiplication in Boolean coordinates. -/
theorem bilinearVectorValue_gfTwo_mul
    (d : Nat) (hd : d ≠ 0)
    (left right : GaloisField 2 d) (output : Fin d) :
    bilinearVectorValue d (gfTwoBoolMultiplicationTensor d hd)
        (gfTwoBoolCoordinates d hd left)
        (gfTwoBoolCoordinates d hd right) output =
      gfTwoBoolCoordinates d hd (left * right) output := by
  unfold bilinearVectorValue
  calc
    xorFamilyValue (d * d) (fun term =>
        let pair := finProdFinEquiv.symm term
        gfTwoBoolMultiplicationTensor d hd pair.1 pair.2 output &&
          gfTwoBoolCoordinates d hd left pair.1 &&
            gfTwoBoolCoordinates d hd right pair.2) =
      boolXorSum₂ (fun i : Fin d => fun j : Fin d =>
        (gfTwoBoolMultiplicationTensor d hd i j output &&
          gfTwoBoolCoordinates d hd left i) &&
            gfTwoBoolCoordinates d hd right j) :=
      xorFamilyValue_finProd_eq_boolXorSum₂ d
        (fun i : Fin d => fun j : Fin d =>
          (gfTwoBoolMultiplicationTensor d hd i j output &&
            gfTwoBoolCoordinates d hd left i) &&
              gfTwoBoolCoordinates d hd right j)
    _ = gfTwoBoolCoordinates d hd (left * right) output :=
      (gfTwoBoolCoordinates_mul d hd left right output).symm

/-- One tensor-affine Horner step is exactly field multiplication followed by
field addition. -/
theorem bilinearAffineVectorValue_gfTwo
    (d : Nat) (hd : d ≠ 0)
    (left point coefficient : GaloisField 2 d) (output : Fin d) :
    bilinearAffineVectorValue d (gfTwoBoolMultiplicationTensor d hd)
        (gfTwoBoolCoordinates d hd left)
        (gfTwoBoolCoordinates d hd point)
        (gfTwoBoolCoordinates d hd coefficient) output =
      gfTwoBoolCoordinates d hd (left * point + coefficient) output := by
  unfold bilinearAffineVectorValue
  rw [bilinearVectorValue_gfTwo_mul]
  exact (gfTwoBoolCoordinates_add d hd (left * point) coefficient output).symm

/-! ## Horner semantics -/

/-- Field-valued recurrence in exactly the order used by the shared Boolean
bundle. -/
def fieldAffineIterate {F : Type*} [Field F]
    (point initial : F) :
    (steps : Nat) -> (Fin steps -> F) -> F
  | 0, _ => initial
  | steps + 1, coefficients =>
      fieldAffineIterate point initial steps
          (fun stage => coefficients (Fin.castAdd 1 stage)) * point +
        coefficients (Fin.natAdd steps (0 : Fin 1))

/-- The Boolean tensor iteration is the coordinate representation of the
field recurrence. -/
theorem bilinearAffineIterateValue_gfTwo
    (d : Nat) (hd : d ≠ 0)
    (point initial : GaloisField 2 d) :
    forall (steps : Nat) (coefficients : Fin steps -> GaloisField 2 d)
      (output : Fin d),
      bilinearAffineIterateValue d
          (gfTwoBoolMultiplicationTensor d hd)
          (gfTwoBoolCoordinates d hd point)
          (gfTwoBoolCoordinates d hd initial)
          steps
          (fun stage => gfTwoBoolCoordinates d hd (coefficients stage))
          output =
        gfTwoBoolCoordinates d hd
          (fieldAffineIterate point initial steps coefficients) output
  | 0, coefficients, output => by
      rfl
  | steps + 1, coefficients, output => by
      unfold bilinearAffineIterateValue fieldAffineIterate
      have hstep := bilinearAffineVectorValue_gfTwo d hd
        (fieldAffineIterate point initial steps
          (fun stage => coefficients (Fin.castAdd 1 stage)))
        point (coefficients (Fin.natAdd steps (0 : Fin 1))) output
      rw [← hstep]
      apply congrArg (fun state : Bitstring d =>
        bilinearAffineVectorValue d
          (gfTwoBoolMultiplicationTensor d hd) state
          (gfTwoBoolCoordinates d hd point)
          (gfTwoBoolCoordinates d hd
            (coefficients (Fin.natAdd steps (0 : Fin 1)))) output)
      funext bit
      exact bilinearAffineIterateValue_gfTwo d hd point initial steps
        (fun stage => coefficients (Fin.castAdd 1 stage)) bit

/-- Descending Horner evaluation of coefficient vector
`a_0, ..., a_steps`. -/
def fieldDescendingHorner {F : Type*} [Field F]
    (steps : Nat) (coefficients : Fin (steps + 1) -> F) (point : F) : F :=
  fieldAffineIterate point (coefficients (Fin.last steps)) steps
    (fun stage => coefficients (Fin.castSucc (Fin.rev stage)))

/-- Removing the low coefficient from descending Horner shifts the remaining
coefficient vector by one. -/
theorem fieldDescendingHorner_succ {F : Type*} [Field F]
    (steps : Nat) (coefficients : Fin (steps + 2) -> F) (point : F) :
    fieldDescendingHorner (steps + 1) coefficients point =
      fieldDescendingHorner steps (fun index => coefficients index.succ) point *
        point + coefficients 0 := by
  unfold fieldDescendingHorner
  change
    fieldAffineIterate point (coefficients (Fin.last (steps + 1))) steps
          (fun stage => coefficients
            (Fin.castSucc (Fin.rev (Fin.castAdd 1 stage)))) * point +
        coefficients
          (Fin.castSucc (Fin.rev (Fin.natAdd steps (0 : Fin 1)))) =
      fieldAffineIterate point (coefficients (Fin.last steps).succ) steps
          (fun stage => coefficients (Fin.castSucc (Fin.rev stage)).succ) *
        point + coefficients 0
  have hinitial : (Fin.last (steps + 1) : Fin (steps + 2)) =
      (Fin.last steps).succ := by
    apply Fin.ext
    rfl
  have hstage : forall stage : Fin steps,
      (Fin.castSucc (Fin.rev (Fin.castAdd 1 stage)) : Fin (steps + 2)) =
        (Fin.castSucc (Fin.rev stage)).succ := by
    intro stage
    apply Fin.ext
    simp [Fin.rev]
    omega
  have hlast :
      (Fin.castSucc (Fin.rev (Fin.natAdd steps (0 : Fin 1))) :
          Fin (steps + 2)) = 0 := by
    apply Fin.ext
    simp [Fin.rev]
  rw [hinitial, hlast]
  apply congrArg (fun value : F => value * point + coefficients 0)
  apply congrArg
  funext stage
  rw [hstage]

/-- Descending Horner equals the usual finite power sum. -/
theorem fieldDescendingHorner_eq_sum {F : Type*} [Field F] :
    forall (steps : Nat) (coefficients : Fin (steps + 1) -> F) (point : F),
      fieldDescendingHorner steps coefficients point =
        ∑ index : Fin (steps + 1),
          coefficients index * point ^ (index : Nat)
  | 0, coefficients, point => by
      simp [fieldDescendingHorner, fieldAffineIterate]
  | steps + 1, coefficients, point => by
      rw [fieldDescendingHorner_succ]
      rw [fieldDescendingHorner_eq_sum]
      calc
        (∑ index : Fin (steps + 1),
              coefficients index.succ * point ^ (index : Nat)) * point +
            coefficients 0 =
          coefficients 0 +
            ∑ index : Fin (steps + 1),
              coefficients index.succ * point ^ (index.succ : Nat) := by
          rw [add_comm]
          apply congrArg (fun value : F => coefficients 0 + value)
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro index _
          simp only [Fin.val_succ, pow_succ]
          ring
        _ = ∑ index : Fin (steps + 2),
            coefficients index * point ^ (index : Nat) := by
          simpa using
            (Fin.sum_univ_succ (fun index : Fin (steps + 2) =>
              coefficients index * point ^ (index : Nat))).symm

/-- Decode coefficient block `coefficient` from a complete circuit input. -/
def jointCoefficientField
    (steps d : Nat) (hd : d ≠ 0)
    (input : Bitstring (polynomialJointInputBits steps d))
    (coefficient : Fin (steps + 1)) : GaloisField 2 d :=
  (gfTwoBoolCoordinates d hd).symm
    (polynomialCoefficientValue steps d input coefficient)

/-- Decode the final point block from a complete circuit input. -/
def jointPointField
    (steps d : Nat) (hd : d ≠ 0)
    (input : Bitstring (polynomialJointInputBits steps d)) :
    GaloisField 2 d :=
  (gfTwoBoolCoordinates d hd).symm
    (polynomialPointValue steps d input)

/-- The bounded-degree polynomial whose coefficients are the structured input
blocks of the complete circuit input. -/
def jointInputPolynomial
    (steps d : Nat) (hd : d ≠ 0)
    (input : Bitstring (polynomialJointInputBits steps d)) :
    Polynomial.degreeLT (GaloisField 2 d) (steps + 1) :=
  (Polynomial.degreeLTEquiv (GaloisField 2 d) (steps + 1)).symm
    (jointCoefficientField steps d hd input)

@[simp]
theorem jointInputPolynomial_coefficient
    (steps d : Nat) (hd : d ≠ 0)
    (input : Bitstring (polynomialJointInputBits steps d))
    (coefficient : Fin (steps + 1)) :
    Polynomial.degreeLTEquiv (GaloisField 2 d) (steps + 1)
        (jointInputPolynomial steps d hd input) coefficient =
      jointCoefficientField steps d hd input coefficient := by
  rw [jointInputPolynomial, LinearEquiv.apply_symm_apply]

/-- Recursive Boolean Horner evaluation is the chosen-basis representation
of descending field Horner on the decoded blocks. -/
theorem polynomialHornerValue_eq_gfTwo_fieldDescendingHorner
    (steps d : Nat) (hd : d ≠ 0)
    (input : Bitstring (polynomialJointInputBits steps d))
    (output : Fin d) :
    polynomialHornerValue steps d
        (gfTwoBoolMultiplicationTensor d hd) input output =
      gfTwoBoolCoordinates d hd
        (fieldDescendingHorner steps
          (jointCoefficientField steps d hd input)
          (jointPointField steps d hd input)) output := by
  unfold polynomialHornerValue fieldDescendingHorner
  have hsemantics := bilinearAffineIterateValue_gfTwo d hd
    (jointPointField steps d hd input)
    (jointCoefficientField steps d hd input (Fin.last steps))
    steps
    (fun stage => jointCoefficientField steps d hd input
      (Fin.castSucc (Fin.rev stage))) output
  simpa [jointPointField, jointCoefficientField] using hsemantics

/-- The field Horner value of the decoded blocks is exactly Mathlib's
polynomial evaluation. -/
theorem fieldDescendingHorner_jointInputPolynomial
    (steps d : Nat) (hd : d ≠ 0)
    (input : Bitstring (polynomialJointInputBits steps d)) :
    fieldDescendingHorner steps
        (jointCoefficientField steps d hd input)
        (jointPointField steps d hd input) =
      (jointInputPolynomial steps d hd input).1.eval
        (jointPointField steps d hd input) := by
  rw [fieldDescendingHorner_eq_sum]
  symm
  simpa using
    (Polynomial.eval_eq_sum_degreeLTEquiv
      (jointInputPolynomial steps d hd input).2
      (jointPointField steps d hd input))

/-- Capstone semantic bridge from the complete Boolean Horner bundle to
finite-field polynomial evaluation. -/
theorem polynomialHornerValue_eq_gfTwo_polynomialEval
    (steps d : Nat) (hd : d ≠ 0)
    (input : Bitstring (polynomialJointInputBits steps d))
    (output : Fin d) :
    polynomialHornerValue steps d
        (gfTwoBoolMultiplicationTensor d hd) input output =
      gfTwoBoolCoordinates d hd
        ((jointInputPolynomial steps d hd input).1.eval
          (jointPointField steps d hd input)) output := by
  rw [polynomialHornerValue_eq_gfTwo_fieldDescendingHorner,
    fieldDescendingHorner_jointInputPolynomial]

/-! ## Specialization to `(seed,index)` inputs -/

@[simp]
theorem polynomialCoefficientValue_seedIndex
    (steps d : Nat) (seed : FiniteBitTape ((steps + 1) * d))
    (index : Fin (2 ^ d)) (coefficient : Fin (steps + 1))
    (bit : Fin d) :
    polynomialCoefficientValue steps d
        (Fin.addCases seed (lexInput d index)) coefficient bit =
      seed (finProdFinEquiv (coefficient, bit)) := by
  simp [polynomialCoefficientValue, polynomialCoefficientInput]

@[simp]
theorem polynomialPointValue_seedIndex
    (steps d : Nat) (seed : FiniteBitTape ((steps + 1) * d))
    (index : Fin (2 ^ d)) (bit : Fin d) :
    polynomialPointValue steps d
        (Fin.addCases seed (lexInput d index)) bit =
      lexInput d index bit := by
  simp [polynomialPointValue, polynomialPointInput]

@[simp]
theorem jointPointField_seedIndex
    (steps d : Nat) (hd : d ≠ 0)
    (seed : FiniteBitTape ((steps + 1) * d))
    (index : Fin (2 ^ d)) :
    jointPointField steps d hd (Fin.addCases seed (lexInput d index)) =
      structuredTruthTableNode d hd index := by
  unfold jointPointField structuredTruthTableNode
  apply congrArg (gfTwoBoolCoordinates d hd).symm
  funext bit
  exact polynomialPointValue_seedIndex steps d seed index bit

@[simp]
theorem jointInputPolynomial_seedIndex
    (steps d : Nat) (hd : d ≠ 0)
    (seed : FiniteBitTape ((steps + 1) * d))
    (index : Fin (2 ^ d)) :
    jointInputPolynomial steps d hd (Fin.addCases seed (lexInput d index)) =
      structuredPolynomialBitSeedEquiv (steps + 1) d hd seed := by
  apply (Polynomial.degreeLTEquiv (GaloisField 2 d) (steps + 1)).injective
  funext coefficient
  rw [jointInputPolynomial_coefficient,
    structuredPolynomialBitSeedEquiv_coefficient]
  unfold jointCoefficientField
  apply congrArg (gfTwoBoolCoordinates d hd).symm
  funext bit
  exact polynomialCoefficientValue_seedIndex
    steps d seed index coefficient bit

/-! ## The actual common-seed coordinate primitive -/

/-- The common bounded-independence degree used by both halves of the DPTW
pair.  The extra one makes `steps + 1` syntactically positive even at `m=0`. -/
def structuredIndependence (m : Nat) : Nat := 4 * m + 1

/-- Polynomial-size coordinate primitive with coefficient-major seed and the
canonical `t`-bit zero-prefix decoder. -/
def structuredDyadicPrimitive
    (n m t : Nat) (hn : 0 < n) (ht : t ≤ n) :
    DPTWCoordinatePrimitive n (structuredIndependence m * n) :=
  polynomialZeroPrefixPrimitive (4 * m) n hn
    (gfTwoBoolMultiplicationTensor n (Nat.ne_of_gt hn)) t
    (prefixPosition n t ht)

/-- The half-field (`p=1/2`) member of the common-seed pair. -/
def structuredUnbiasedPrimitive
    (n m : Nat) (hn : 0 < n) :
    DPTWCoordinatePrimitive n (structuredIndependence m * n) :=
  structuredDyadicPrimitive n m 1 hn (by omega)

private theorem bool_eq_of_eq_false_iff (left right : Bool)
    (hfalse : left = false ↔ right = false) : left = right := by
  cases left <;> cases right <;> simp_all

/-- The circuit primitive's generator is exactly the structured finite-field
source thresholded by the canonical prefix-zero set. -/
theorem structuredDyadicPrimitive_generate
    (n m t : Nat) (hn : 0 < n) (ht : t ≤ n) :
    (structuredDyadicPrimitive n m t hn ht).generate =
      structuredPolynomialSubsetSource n (structuredIndependence m)
        (Nat.ne_of_gt hn)
        (zeroPrefixFalseSet n t (Nat.ne_of_gt hn) ht) := by
  funext seed index
  apply bool_eq_of_eq_false_iff
  calc
    (structuredDyadicPrimitive n m t hn ht).generate seed index = false ↔
        forall selected : Fin t,
          polynomialHornerValue (4 * m) n
              (gfTwoBoolMultiplicationTensor n (Nat.ne_of_gt hn))
              (Fin.addCases seed (lexInput n index))
              (prefixPosition n t ht selected) = false :=
      polynomialZeroPrefixPrimitive_generate_eq_false_iff
        (4 * m) n hn
        (gfTwoBoolMultiplicationTensor n (Nat.ne_of_gt hn))
        t (prefixPosition n t ht) seed index
    _ ↔ forall selected : Fin t,
        gfTwoBoolCoordinates n (Nat.ne_of_gt hn)
          ((structuredPolynomialBitSeedEquiv
              (structuredIndependence m) n (Nat.ne_of_gt hn) seed).1.eval
            (structuredTruthTableNode n (Nat.ne_of_gt hn) index))
          (prefixPosition n t ht selected) = false := by
      constructor
      · intro h selected
        have hselected := h selected
        rw [polynomialHornerValue_eq_gfTwo_polynomialEval] at hselected
        simpa [structuredIndependence] using hselected
      · intro h selected
        rw [polynomialHornerValue_eq_gfTwo_polynomialEval]
        simpa [structuredIndependence] using h selected
    _ ↔
        (structuredPolynomialBitSeedEquiv
              (structuredIndependence m) n (Nat.ne_of_gt hn) seed).1.eval
            (structuredTruthTableNode n (Nat.ne_of_gt hn) index) ∈
          zeroPrefixFalseSet n t (Nat.ne_of_gt hn) ht := by
      exact (mem_zeroPrefixFalseSet n t (Nat.ne_of_gt hn) ht _).symm
    _ ↔ structuredPolynomialSubsetSource n (structuredIndependence m)
          (Nat.ne_of_gt hn)
          (zeroPrefixFalseSet n t (Nat.ne_of_gt hn) ht) seed index = false := by
      change
        _ ∈ zeroPrefixFalseSet n t (Nat.ne_of_gt hn) ht ↔
          fieldSubsetCoin
              (zeroPrefixFalseSet n t (Nat.ne_of_gt hn) ht) _ = false
      exact (fieldSubsetCoin_eq_false_iff _ _).symm

/-- The actual primitive has the exact `(4m+1)`-wise dyadic product law. -/
theorem structuredDyadicPrimitive_patternFalseBiased
    (n m t : Nat) (hn : 0 < n) (ht : t ≤ n) :
    IsKWisePatternFalseBiased (structuredIndependence m)
      (1 / (2 : Rat) ^ t)
      (structuredDyadicPrimitive n m t hn ht).generate := by
  rw [structuredDyadicPrimitive_generate]
  have hlaw := structuredPolynomialSubsetSource_isKWisePatternFalseBiased
    n (structuredIndependence m) (Nat.ne_of_gt hn)
    (zeroPrefixFalseSet n t (Nat.ne_of_gt hn) ht)
  rw [zeroPrefixFalseSet_exactMass n t (Nat.ne_of_gt hn) ht] at hlaw
  exact hlaw

/-- The `t=1` specialization is exactly unbiased on every cylinder up to the
common independence degree. -/
theorem structuredUnbiasedPrimitive_patternUnbiased
    (n m : Nat) (hn : 0 < n) :
    IsKWisePatternUnbiased (structuredIndependence m)
      (structuredUnbiasedPrimitive n m hn).generate := by
  intro support hcard pattern
  have hbiased := structuredDyadicPrimitive_patternFalseBiased
    n m 1 hn (by omega) support hcard pattern
  change finiteAverage (fun seed =>
      localPatternIndicator support pattern
        ((structuredUnbiasedPrimitive n m hn).generate seed)) = _
  change finiteAverage (fun seed =>
      localPatternIndicator support pattern
        ((structuredDyadicPrimitive n m 1 hn (by omega)).generate seed)) = _
  rw [hbiased]
  norm_num
  simpa [one_div] using
    (DPTWFiniteFieldKWiseSeed.localPatternProductMass_half pattern)

/-- Monotonicity of exact biased cylinder laws in the query count. -/
theorem isKWisePatternFalseBiased_of_le
    {seed coordinates small large : Nat} {p : Rat}
    {source : FiniteBitTape seed -> Fin coordinates -> Bool}
    (hsmall : small ≤ large)
    (hlaw : IsKWisePatternFalseBiased large p source) :
    IsKWisePatternFalseBiased small p source := by
  intro support hcard pattern
  exact hlaw support (hcard.trans hsmall) pattern

/-- Monotonicity of exact unbiased cylinder laws in the query count. -/
theorem isKWisePatternUnbiased_of_le
    {seed coordinates small large : Nat}
    {source : FiniteBitTape seed -> Fin coordinates -> Bool}
    (hsmall : small ≤ large)
    (hlaw : IsKWisePatternUnbiased large source) :
    IsKWisePatternUnbiased small source := by
  intro support hcard pattern
  exact hlaw support (hcard.trans hsmall) pattern

/-- A singleton cylinder extracts the exact true marginal from any positive
query-count biased product law. -/
theorem uniformCoordinateMarginal_of_patternFalseBiased
    {seed coordinates independence : Nat} {p : Rat}
    {source : FiniteBitTape seed -> Fin coordinates -> Bool}
    (hpositive : 1 ≤ independence)
    (hlaw : IsKWisePatternFalseBiased independence p source)
    (coordinate : Fin coordinates) :
    uniformPredicateAverage (fun randomSeed =>
      source randomSeed coordinate) = 1 - p := by
  let support : Finset (Fin coordinates) := {coordinate}
  let pattern : LocalAssignment support := fun _ => true
  have hpattern := hlaw support (by simp [support, hpositive]) pattern
  calc
    uniformPredicateAverage (fun randomSeed =>
        source randomSeed coordinate) =
      finiteAverage (fun randomSeed : FiniteBitTape seed =>
        localPatternIndicator support pattern (source randomSeed)) := by
      unfold uniformPredicateAverage finiteAverage
      congr 1
      apply Finset.sum_congr rfl
      intro randomSeed _
      unfold boolIndicator localPatternIndicator
      dsimp only
      cases hvalue : source randomSeed coordinate
      · rw [if_neg (by simp)]
        rw [if_neg]
        intro hequal
        have hcoordinate := congrFun hequal
          (⟨coordinate, by simp [support]⟩ : support)
        change source randomSeed coordinate = true at hcoordinate
        rw [hvalue] at hcoordinate
        contradiction
      · rw [if_pos (by simp)]
        rw [if_pos]
        funext localCoordinate
        have hmem := localCoordinate.property
        change (localCoordinate : Fin coordinates) ∈
          ({coordinate} : Finset (Fin coordinates)) at hmem
        have heq : (localCoordinate : Fin coordinates) = coordinate :=
          Finset.mem_singleton.mp hmem
        change source randomSeed localCoordinate = true
        rw [heq, hvalue]
    _ = localPatternProductMass p pattern := hpattern
    _ = 1 - p := by
      simp [localPatternProductMass, support, pattern]

/-- Exact true marginal of every coordinate of the biased structured
primitive. -/
theorem structuredDyadicPrimitive_uniformCoordinateMarginal
    (n m t : Nat) (hn : 0 < n) (ht : t ≤ n)
    (coordinate : Fin (2 ^ n)) :
    uniformPredicateAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) =>
      (structuredDyadicPrimitive n m t hn ht).generate seed coordinate) =
      1 - 1 / (2 : Rat) ^ t := by
  apply uniformCoordinateMarginal_of_patternFalseBiased
    (independence := structuredIndependence m)
  · unfold structuredIndependence
    omega
  · exact structuredDyadicPrimitive_patternFalseBiased n m t hn ht

/-- Polynomial joint-coordinate gate bound of the actual structured
primitive. -/
theorem structuredDyadicPrimitive_jointCircuit_gateCount_le
    (n m t : Nat) (hn : 0 < n) (ht : t ≤ n) :
    (structuredDyadicPrimitive n m t hn ht).jointCircuit.gateCount ≤
      (4 * m) * (n * (6 + 6 * (n * n))) + (2 + t) := by
  exact polynomialZeroPrefixPrimitive_jointCircuit_gateCount_le
    (4 * m) n hn (gfTwoBoolMultiplicationTensor n (Nat.ne_of_gt hn))
    t (prefixPosition n t ht)

/-- Complete common-seed A/B package.  Both actual primitives have the same
seed type `FiniteBitTape ((4m+1)*n)`; the stronger common law is weakened to
the `4m` and `2m` query counts consumed downstream. -/
theorem structuredDPTWPair_exactLaws
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n) :
    IsKWisePatternUnbiased (4 * m)
        (structuredUnbiasedPrimitive n m hn).generate ∧
      IsKWisePatternFalseBiased (2 * m)
        (1 / (2 : Rat) ^ tailBits)
        (structuredDyadicPrimitive n m tailBits hn htail).generate ∧
      forall coordinate : Fin (2 ^ n),
        uniformPredicateAverage (fun seed :
            FiniteBitTape (structuredIndependence m * n) =>
          (structuredDyadicPrimitive n m tailBits hn htail).generate
            seed coordinate) =
          1 - 1 / (2 : Rat) ^ tailBits := by
  refine ⟨?_, ?_, ?_⟩
  · apply isKWisePatternUnbiased_of_le
      (large := structuredIndependence m)
    · unfold structuredIndependence
      omega
    · exact structuredUnbiasedPrimitive_patternUnbiased n m hn
  · apply isKWisePatternFalseBiased_of_le
      (large := structuredIndependence m)
    · unfold structuredIndependence
      omega
    · exact structuredDyadicPrimitive_patternFalseBiased
        n m tailBits hn htail
  · exact structuredDyadicPrimitive_uniformCoordinateMarginal
      n m tailBits hn htail

#print axioms structuredPolynomialSubsetSource_isKWisePatternFalseBiased
#print axioms zeroPrefixFalseSet_exactMass
#print axioms bilinearVectorValue_gfTwo_mul
#print axioms polynomialHornerValue_eq_gfTwo_polynomialEval
#print axioms structuredDyadicPrimitive_generate
#print axioms structuredDyadicPrimitive_jointCircuit_gateCount_le
#print axioms structuredDPTWPair_exactLaws

end DPTWStructuredFieldCoordinatePrimitive

end

end OneTapeMagnification
end Frontier
end Pnp4
