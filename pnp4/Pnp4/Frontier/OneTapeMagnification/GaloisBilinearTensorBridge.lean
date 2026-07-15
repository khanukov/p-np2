import Mathlib.FieldTheory.Finite.GaloisField

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open scoped BigOperators

namespace GaloisBilinearTensorBridge

/-!
# A bilinear Boolean tensor for multiplication in `GF(2^d)`

This file turns the finite-dimensional `ZMod 2`-algebra structure of
`GaloisField 2 d` into explicit Boolean coordinates.  The basis itself is
classically chosen, but once it is fixed, multiplication has exactly `d^2`
fixed tensor terms per output coordinate.  Thus the theorem below is the
algebraic API needed to implement Horner evaluation nonuniformly with XOR and
AND gates; it does not by itself construct a uniform basis-finding algorithm.

This is infrastructure for a bounded-independence source, not a circuit lower
bound and not mainline progress toward `P != NP`.
-/

/-- The standard two-element-ring carrier, presented as a Boolean. -/
def zmodTwoEquivBool : ZMod 2 ≃ Bool :=
  (ZMod.finEquiv 2).symm.toEquiv.trans finTwoEquiv

@[simp]
theorem zmodTwoEquivBool_zero : zmodTwoEquivBool 0 = false := by
  rfl

@[simp]
theorem zmodTwoEquivBool_one : zmodTwoEquivBool 1 = true := by
  rfl

/-- Addition in `ZMod 2` is Boolean XOR under the standard equivalence. -/
theorem zmodTwoEquivBool_add (a b : ZMod 2) :
    zmodTwoEquivBool (a + b) = (zmodTwoEquivBool a).xor (zmodTwoEquivBool b) := by
  obtain ⟨i, rfl⟩ := (ZMod.finEquiv 2).surjective a
  obtain ⟨j, rfl⟩ := (ZMod.finEquiv 2).surjective b
  change finTwoEquiv ((ZMod.finEquiv 2).symm
      (ZMod.finEquiv 2 i + ZMod.finEquiv 2 j)) =
    (finTwoEquiv i).xor (finTwoEquiv j)
  rw [← map_add, RingEquiv.symm_apply_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-- Multiplication in `ZMod 2` is Boolean AND under the standard equivalence. -/
theorem zmodTwoEquivBool_mul (a b : ZMod 2) :
    zmodTwoEquivBool (a * b) = (zmodTwoEquivBool a && zmodTwoEquivBool b) := by
  obtain ⟨i, rfl⟩ := (ZMod.finEquiv 2).surjective a
  obtain ⟨j, rfl⟩ := (ZMod.finEquiv 2).surjective b
  change finTwoEquiv ((ZMod.finEquiv 2).symm
      (ZMod.finEquiv 2 i * ZMod.finEquiv 2 j)) =
    (finTwoEquiv i && finTwoEquiv j)
  rw [← map_mul, RingEquiv.symm_apply_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-- A classically chosen `ZMod 2`-basis of `GF(2^d)`. -/
noncomputable def gfTwoBasis (d : Nat) (hd : d ≠ 0) :
    Basis (Fin d) (ZMod 2) (GaloisField 2 d) :=
  Module.finBasisOfFinrankEq (ZMod 2) (GaloisField 2 d)
    (GaloisField.finrank 2 hd)

/-- Coordinates of `GF(2^d)` in the classically chosen basis. -/
noncomputable def gfTwoCoordinates (d : Nat) (hd : d ≠ 0) :
    GaloisField 2 d ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
  (gfTwoBasis d hd).equivFun

/-- Pointwise conversion between `ZMod 2`-vectors and Boolean vectors. -/
def zmodTwoVectorEquivBool (d : Nat) :
    (Fin d → ZMod 2) ≃ (Fin d → Bool) where
  toFun vector i := zmodTwoEquivBool (vector i)
  invFun vector i := zmodTwoEquivBool.symm (vector i)
  left_inv vector := by
    funext i
    exact zmodTwoEquivBool.symm_apply_apply (vector i)
  right_inv vector := by
    funext i
    exact zmodTwoEquivBool.apply_symm_apply (vector i)

/-- The chosen field coordinates, with each `ZMod 2` coefficient presented
as a Boolean.  This is an actual equivalence, so in particular it is a
bijection suitable for a structured coefficient seed. -/
noncomputable def gfTwoBoolCoordinates (d : Nat) (hd : d ≠ 0) :
    GaloisField 2 d ≃ (Fin d → Bool) :=
  (gfTwoCoordinates d hd).toEquiv.trans (zmodTwoVectorEquivBool d)

@[simp]
theorem gfTwoBoolCoordinates_apply (d : Nat) (hd : d ≠ 0)
    (x : GaloisField 2 d) (i : Fin d) :
    gfTwoBoolCoordinates d hd x i =
      zmodTwoEquivBool (gfTwoCoordinates d hd x i) :=
  rfl

theorem gfTwoBoolCoordinates_add (d : Nat) (hd : d ≠ 0)
    (x y : GaloisField 2 d) (i : Fin d) :
    gfTwoBoolCoordinates d hd (x + y) i =
      (gfTwoBoolCoordinates d hd x i).xor (gfTwoBoolCoordinates d hd y i) := by
  rw [gfTwoBoolCoordinates_apply, gfTwoBoolCoordinates_apply,
    gfTwoBoolCoordinates_apply, map_add]
  change zmodTwoEquivBool
      (gfTwoCoordinates d hd x i + gfTwoCoordinates d hd y i) = _
  exact zmodTwoEquivBool_add _ _

theorem gfTwoBoolCoordinates_bijective (d : Nat) (hd : d ≠ 0) :
    Function.Bijective (gfTwoBoolCoordinates d hd) :=
  (gfTwoBoolCoordinates d hd).bijective

/-- Decoding a Boolean coefficient vector is the corresponding basis sum. -/
theorem gfTwoBoolCoordinates_symm_eq_sum (d : Nat) (hd : d ≠ 0)
    (bits : Fin d → Bool) :
    (gfTwoBoolCoordinates d hd).symm bits =
      ∑ i : Fin d, zmodTwoEquivBool.symm (bits i) • gfTwoBasis d hd i := by
  change (gfTwoCoordinates d hd).symm
      (fun i => zmodTwoEquivBool.symm (bits i)) = _
  exact (gfTwoBasis d hd).equivFun_symm_apply _

/-- The fixed multiplication tensor in the chosen basis. -/
noncomputable def gfTwoMultiplicationTensor (d : Nat) (hd : d ≠ 0)
    (i j r : Fin d) : ZMod 2 :=
  gfTwoCoordinates d hd (gfTwoBasis d hd i * gfTwoBasis d hd j) r

/-- Boolean presentation of the fixed multiplication tensor. -/
noncomputable def gfTwoBoolMultiplicationTensor (d : Nat) (hd : d ≠ 0)
    (i j r : Fin d) : Bool :=
  zmodTwoEquivBool (gfTwoMultiplicationTensor d hd i j r)

/-- XOR of a finite Boolean family.  The definition uses `ZMod 2` addition;
`zmodTwoEquivBool_add` proves that every such addition is exactly Boolean XOR. -/
noncomputable def boolXorSum {ι : Type*} [Fintype ι] (f : ι → Bool) : Bool :=
  zmodTwoEquivBool (∑ i, zmodTwoEquivBool.symm (f i))

theorem boolXorSum_bool (f : Bool → Bool) :
    boolXorSum f = (f true).xor (f false) := by
  rw [boolXorSum, Fintype.sum_bool, zmodTwoEquivBool_add]
  simp

/-- Iterated XOR over a rectangular finite family. -/
noncomputable def boolXorSum₂ {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → Bool) : Bool :=
  boolXorSum (fun i => boolXorSum (f i))

theorem boolXorSum₂_eq (ι κ : Type*) [Fintype ι] [Fintype κ]
    (f : ι → κ → Bool) :
    boolXorSum₂ f =
      zmodTwoEquivBool
        (∑ i : ι, ∑ j : κ, zmodTwoEquivBool.symm (f i j)) := by
  simp [boolXorSum₂, boolXorSum]

theorem gfTwoCoordinates_mul (d : Nat) (hd : d ≠ 0)
    (x y : GaloisField 2 d) (r : Fin d) :
    gfTwoCoordinates d hd (x * y) r =
      ∑ i : Fin d, ∑ j : Fin d,
        gfTwoMultiplicationTensor d hd i j r *
          gfTwoCoordinates d hd x i * gfTwoCoordinates d hd y j := by
  let b := gfTwoBasis d hd
  let c := gfTwoCoordinates d hd
  change c (x * y) r =
    ∑ i : Fin d, ∑ j : Fin d, c (b i * b j) r * c x i * c y j
  have hx : (∑ i : Fin d, c x i • b i) = x :=
    (gfTwoBasis d hd).sum_equivFun x
  have hy : (∑ j : Fin d, c y j • b j) = y :=
    (gfTwoBasis d hd).sum_equivFun y
  calc
    c (x * y) r =
        c ((∑ i : Fin d, c x i • b i) * (∑ j : Fin d, c y j • b j)) r := by
      rw [hx, hy]
    _ = ∑ j : Fin d, ∑ i : Fin d, c (b i * b j) r * c x i * c y j := by
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smul,
        Pi.smul_apply, smul_eq_mul]
      ring
    _ = ∑ i : Fin d, ∑ j : Fin d, c (b i * b j) r * c x i * c y j := by
      rw [Finset.sum_comm]

/-- In Boolean coordinates, every output bit of field multiplication is the
XOR over all input-coordinate pairs of one fixed tensor bit AND the two input
bits. -/
theorem gfTwoBoolCoordinates_mul (d : Nat) (hd : d ≠ 0)
    (x y : GaloisField 2 d) (r : Fin d) :
    gfTwoBoolCoordinates d hd (x * y) r =
      boolXorSum₂ (fun i : Fin d => fun j : Fin d =>
        (gfTwoBoolMultiplicationTensor d hd i j r &&
          gfTwoBoolCoordinates d hd x i) &&
            gfTwoBoolCoordinates d hd y j) := by
  rw [gfTwoBoolCoordinates_apply, boolXorSum₂_eq]
  apply congrArg zmodTwoEquivBool
  rw [gfTwoCoordinates_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change gfTwoMultiplicationTensor d hd i j r *
      gfTwoCoordinates d hd x i * gfTwoCoordinates d hd y j =
    zmodTwoEquivBool.symm
      ((zmodTwoEquivBool (gfTwoMultiplicationTensor d hd i j r) &&
        zmodTwoEquivBool (gfTwoCoordinates d hd x i)) &&
          zmodTwoEquivBool (gfTwoCoordinates d hd y j))
  rw [← zmodTwoEquivBool_mul, ← zmodTwoEquivBool_mul,
    zmodTwoEquivBool.symm_apply_apply]

end GaloisBilinearTensorBridge
end OneTapeMagnification
end Frontier
end Pnp4
