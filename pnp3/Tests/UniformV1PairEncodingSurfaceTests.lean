import Complexity.Uniform.V1.PairEncoding

/-!
# Uniform V1 uniquely-decodable pair-codec surface tests

Definition pins and explicit full-proposition wrappers for the P2-1 codec.
Axiom roots live only in the central `Tests/AxiomsAudit.lean`.
-/

namespace Pnp3.Tests.UniformV1PairEncoding

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding

#check tagList
#check encodePairList
#check decodePairList
#check pairLength
#check DecodedPair
#check EncodedWord
#check encodePair
#check decodePair

#check tagList_length
#check encodePairList_length
#check tagList_tag
#check tagList_data
#check encodePairList_tag
#check encodePairList_data
#check encodePairList_separator
#check encodePairList_witness
#check encodePairList_boundary
#check decodePairList_roundtrip
#check decodePairList_eq_some_iff
#check decodePairList_eq_none_iff
#check encodePairList_injective
#check decodePairList_tagList_none
#check decodePairList_dangling_false_none
#check decodePairList_nil
#check decodePairList_false
#check decodePairList_false_true
#check decodePairList_true
#check decodePairList_true_false
#check encodePairList_two_one
#check decodePairList_two_one
#check pairLength_eq
#check encodePair_tag
#check encodePair_data
#check encodePair_separator
#check encodePair_witness
#check encodePair_boundary
#check encodePair_toList
#check decodePair_roundtrip
#check encodePair_packed_injective
#check encodePair_injective
#check initialConfig_pair_tag
#check initialConfig_pair_data
#check initialConfig_pair_separator
#check initialConfig_pair_witness
#check initialConfig_pair_padding
#check decodePair_empty
#check decodePair_two_one

theorem check_tagList_length (xs : List Bool) :
    (tagList xs).length = 2 * xs.length :=
  tagList_length xs

theorem check_encodePairList_length (xs ws : List Bool) :
    (encodePairList xs ws).length = 2 * xs.length + 1 + ws.length :=
  encodePairList_length xs ws

theorem check_tagList_tag (xs : List Bool) (i : Fin xs.length) :
    (tagList xs).get ⟨2 * i.val, by rw [tagList_length]; omega⟩ = false :=
  tagList_tag xs i

theorem check_tagList_data (xs : List Bool) (i : Fin xs.length) :
    (tagList xs).get ⟨2 * i.val + 1, by simp [tagList_length]; omega⟩ = xs.get i :=
  tagList_data xs i

theorem check_encodePairList_tag (xs ws : List Bool) (i : Fin xs.length) :
    (encodePairList xs ws).get
      ⟨2 * i.val, by simp [encodePairList_length]; omega⟩ = false :=
  encodePairList_tag xs ws i

theorem check_encodePairList_data (xs ws : List Bool) (i : Fin xs.length) :
    (encodePairList xs ws).get
      ⟨2 * i.val + 1, by simp [encodePairList_length]; omega⟩ = xs.get i :=
  encodePairList_data xs ws i

theorem check_encodePairList_separator (xs ws : List Bool) :
    (encodePairList xs ws).get
      ⟨2 * xs.length, by rw [encodePairList_length]; omega⟩ = true :=
  encodePairList_separator xs ws

theorem check_encodePairList_witness (xs ws : List Bool) (j : Fin ws.length) :
    (encodePairList xs ws).get
      ⟨2 * xs.length + 1 + j.val, by rw [encodePairList_length]; omega⟩ = ws.get j :=
  encodePairList_witness xs ws j

theorem check_encodePairList_boundary (xs ws : List Bool) :
    (encodePairList xs ws).take (2 * xs.length) = tagList xs ∧
    (encodePairList xs ws).drop (2 * xs.length) = true :: ws :=
  encodePairList_boundary xs ws

theorem check_decodePairList_roundtrip (xs ws : List Bool) :
    decodePairList (encodePairList xs ws) = some (xs, ws) :=
  decodePairList_roundtrip xs ws

theorem check_decodePairList_eq_some_iff (l xs ws : List Bool) :
    decodePairList l = some (xs, ws) ↔ l = encodePairList xs ws :=
  decodePairList_eq_some_iff l xs ws

theorem check_decodePairList_eq_none_iff (l : List Bool) :
    decodePairList l = none ↔ ¬ ∃ xs ws, l = encodePairList xs ws :=
  decodePairList_eq_none_iff l

theorem check_encodePairList_injective :
    Function.Injective (Function.uncurry encodePairList) :=
  encodePairList_injective

theorem check_decodePairList_tagList_none (xs : List Bool) :
    decodePairList (tagList xs) = none :=
  decodePairList_tagList_none xs

theorem check_decodePairList_dangling_false_none (xs : List Bool) :
    decodePairList (tagList xs ++ [false]) = none :=
  decodePairList_dangling_false_none xs

theorem check_decodePairList_nil : decodePairList [] = none :=
  decodePairList_nil

theorem check_decodePairList_false : decodePairList [false] = none :=
  decodePairList_false

theorem check_decodePairList_false_true : decodePairList [false, true] = none :=
  decodePairList_false_true

theorem check_decodePairList_true : decodePairList [true] = some ([], []) :=
  decodePairList_true

theorem check_decodePairList_true_false :
    decodePairList [true, false] = some ([], [false]) :=
  decodePairList_true_false

theorem check_encodePairList_two_one :
    encodePairList [true, false] [true] = [false, true, false, false, true, true] :=
  encodePairList_two_one

theorem check_decodePairList_two_one :
    decodePairList [false, true, false, false, true, true] =
      some ([true, false], [true]) :=
  decodePairList_two_one

theorem check_pairLength_eq (n m : Nat) :
    pairLength n m = 2 * n + 1 + m :=
  pairLength_eq n m

theorem check_encodePair_tag {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (i : Fin n) :
    encodePair x w ⟨2 * i.val, by simp [pairLength_eq]; omega⟩ = false :=
  encodePair_tag x w i

theorem check_encodePair_data {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (i : Fin n) :
    encodePair x w ⟨2 * i.val + 1, by simp [pairLength_eq]; omega⟩ = x i :=
  encodePair_data x w i

theorem check_encodePair_separator {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    encodePair x w ⟨2 * n, by rw [pairLength_eq]; omega⟩ = true :=
  encodePair_separator x w

theorem check_encodePair_witness {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Fin m) :
    encodePair x w ⟨2 * n + 1 + j.val, by rw [pairLength_eq]; omega⟩ = w j :=
  encodePair_witness x w j

theorem check_encodePair_boundary {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    (∀ i : Fin n,
      encodePair x w ⟨2 * i.val, by simp [pairLength_eq]; omega⟩ = false) ∧
    encodePair x w ⟨2 * n, by rw [pairLength_eq]; omega⟩ = true :=
  encodePair_boundary x w

theorem check_encodePair_toList {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    List.ofFn (encodePair x w) = encodePairList (List.ofFn x) (List.ofFn w) :=
  encodePair_toList x w

theorem check_decodePair_roundtrip {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    decodePair (encodePair x w) =
      some ((⟨n, x⟩, ⟨m, w⟩) : DecodedPair) :=
  decodePair_roundtrip x w

theorem check_encodePair_packed_injective :
    Function.Injective
      (fun p : DecodedPair =>
        (⟨pairLength p.1.1 p.2.1, encodePair p.1.2 p.2.2⟩ : EncodedWord)) :=
  encodePair_packed_injective

theorem check_encodePair_injective {n m : Nat} :
    Function.Injective
      (fun p : Bitstring n × Bitstring m => encodePair p.1 p.2) :=
  encodePair_injective

theorem check_initialConfig_pair_tag (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m) (i : Fin n) :
    (initialConfig M budget (encodePair x w)).tape
      ⟨2 * i.val, by simp [tapeLength, pairLength_eq]; omega⟩ = some false :=
  initialConfig_pair_tag M x w i

theorem check_initialConfig_pair_data (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m) (i : Fin n) :
    (initialConfig M budget (encodePair x w)).tape
      ⟨2 * i.val + 1, by simp [tapeLength, pairLength_eq]; omega⟩ = some (x i) :=
  initialConfig_pair_data M x w i

theorem check_initialConfig_pair_separator (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (initialConfig M budget (encodePair x w)).tape
      ⟨2 * n, by simp only [tapeLength, pairLength_eq]; omega⟩ = some true :=
  initialConfig_pair_separator M x w

theorem check_initialConfig_pair_witness (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m) (j : Fin m) :
    (initialConfig M budget (encodePair x w)).tape
      ⟨2 * n + 1 + j.val, by simp [tapeLength, pairLength_eq]; omega⟩ = some (w j) :=
  initialConfig_pair_witness M x w j

theorem check_initialConfig_pair_padding (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) budget)) (h : pairLength n m ≤ i.val) :
    (initialConfig M budget (encodePair x w)).tape i = none :=
  initialConfig_pair_padding M x w i h

theorem check_decodePair_empty :
    let x : Bitstring 0 := fun i => Fin.elim0 i
    let w : Bitstring 0 := fun i => Fin.elim0 i
    decodePair (encodePair x w) =
      some ((⟨0, x⟩, ⟨0, w⟩) : DecodedPair) :=
  decodePair_empty

theorem check_decodePair_two_one :
    let x : Bitstring 2 := fun i => i.val = 0
    let w : Bitstring 1 := fun _ => true
    List.ofFn (encodePair x w) = [false, true, false, false, true, true] ∧
    decodePair (encodePair x w) =
      some ((⟨2, x⟩, ⟨1, w⟩) : DecodedPair) :=
  decodePair_two_one

end Pnp3.Tests.UniformV1PairEncoding
