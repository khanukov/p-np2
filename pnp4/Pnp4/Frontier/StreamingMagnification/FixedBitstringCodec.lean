import Pnp4.Frontier.StreamingMagnification.TotalSearch
import Batteries.Data.BitVec.Lemmas
import Mathlib.Tactic

/-!
# Exact fixed-length bitstring codec

This module supplies the executable big-endian bijection between a bitstring
of length `length` and `Fin (2 ^ length)`.  Physical position zero is the most
significant bit, matching both `TotalSearch.lexInput` and the serialized order
used by `StreamMerge`.

The definitions are exact at every length, including length zero.  They make
no claim about the running time or circuit complexity of encoding or decoding.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace FixedBitstringCodec

open Pnp3.ComplexityInterfaces

/-- Interpret a fixed-length bitstring as a big-endian finite number. -/
def rank {length : Nat} (bits : Bitstring length) : Fin (2 ^ length) :=
  (BitVec.ofFnBE bits).toFin

/-- Decode a finite number into its exact-length big-endian bitstring. -/
def unrank {length : Nat} (index : Fin (2 ^ length)) : Bitstring length :=
  fun position =>
    (BitVec.ofNatLT index.val index.isLt).getMsb position

/-- Decoding after encoding recovers every fixed-length bitstring. -/
@[simp] theorem unrank_rank {length : Nat} (bits : Bitstring length) :
    unrank (rank bits) = bits := by
  funext position
  change
    (BitVec.ofNatLT (BitVec.ofFnBE bits).toNat _).getMsb position =
      bits position
  rw [BitVec.ofNatLT_toNat]
  exact BitVec.getMsb_ofFnBE bits position

/-- Encoding after decoding recovers every truth-table coordinate. -/
@[simp] theorem rank_unrank {length : Nat} (index : Fin (2 ^ length)) :
    rank (unrank index) = index := by
  apply Fin.ext
  change
    (BitVec.ofFnBE
      (fun position =>
        (BitVec.ofNatLT index.val index.isLt).getMsb position)).toNat =
      index.val
  have hvector :
      BitVec.ofFnBE
        (fun position =>
          (BitVec.ofNatLT index.val index.isLt).getMsb position) =
        BitVec.ofNatLT index.val index.isLt := by
    apply BitVec.eq_of_getMsbD_eq
    intro i hi
    rw [BitVec.getMsbD_ofFnBE]
    simp [hi, BitVec.getMsb, BitVec.getMsbD,
      BitVec.getLsb, BitVec.getLsbD]
  rw [hvector]
  exact BitVec.toNat_ofNatLT index.val index.isLt

/-- The exact executable equivalence underlying `rank` and `unrank`. -/
def equiv (length : Nat) : Bitstring length ≃ Fin (2 ^ length) where
  toFun := rank
  invFun := unrank
  left_inv := unrank_rank
  right_inv := rank_unrank

@[simp] theorem equiv_apply {length : Nat} (bits : Bitstring length) :
    equiv length bits = rank bits :=
  rfl

@[simp] theorem equiv_symm_apply {length : Nat}
    (index : Fin (2 ^ length)) :
    (equiv length).symm index = unrank index :=
  rfl

/-- `rank` is injective; its definition contains no noncomputable choice. -/
theorem rank_injective {length : Nat} :
    Function.Injective (@rank length) :=
  (equiv length).injective

/-- `rank` is surjective; its definition contains no noncomputable choice. -/
theorem rank_surjective {length : Nat} :
    Function.Surjective (@rank length) :=
  (equiv length).surjective

/-- `unrank` is injective; its definition contains no noncomputable choice. -/
theorem unrank_injective {length : Nat} :
    Function.Injective (@unrank length) :=
  (equiv length).symm.injective

/-- `unrank` is surjective; its definition contains no noncomputable choice. -/
theorem unrank_surjective {length : Nat} :
    Function.Surjective (@unrank length) :=
  (equiv length).symm.surjective

/--
The decoder is exactly the lexicographic input convention already used for
truth-table coordinates by `TotalSearch`.
-/
@[simp] theorem unrank_eq_lexInput (length : Nat)
    (index : Fin (2 ^ length)) :
    unrank index = TotalSearch.lexInput length index := by
  funext position
  simp [unrank, TotalSearch.lexInput, BitVec.getMsb, BitVec.getLsb]

/-- Coordinate form of the big-endian decoding convention. -/
@[simp] theorem unrank_apply {length : Nat}
    (index : Fin (2 ^ length)) (position : Fin length) :
    unrank index position =
      Nat.testBit index.val (length - 1 - position.val) := by
  rw [unrank_eq_lexInput]
  rfl

/-- Every lexicographic truth-table input ranks back to its coordinate. -/
@[simp] theorem rank_lexInput (length : Nat)
    (index : Fin (2 ^ length)) :
    rank (TotalSearch.lexInput length index) = index := by
  rw [← unrank_eq_lexInput]
  exact rank_unrank index

end FixedBitstringCodec
end StreamingMagnification
end Frontier
end Pnp4
