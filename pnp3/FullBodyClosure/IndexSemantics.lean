import FullBodyClosure.IndexLoop
namespace FullBodyClosure
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
private def digit (b : Bool) : Nat := if b then 1 else 0
private def numeral : List Bool → Nat
  | [] => 0
  | b::bs => digit b+2*numeral bs
private def accumulate (a : Nat) (bits : List Bool) : Nat := bits.foldl (fun i b=>2*i+digit b) a
private theorem accumulate_snoc (a : Nat) (bits : List Bool) (b : Bool) :
    accumulate a (bits++[b])=2*accumulate a bits+digit b := by
  simp only [accumulate,List.foldl_append,List.foldl_cons,List.foldl_nil]
private theorem reverse_horner (bits : List Bool) : accumulate 0 bits.reverse=numeral bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    rw [List.reverse_cons,accumulate_snoc,ih,numeral]
    omega
private theorem numeral_lt (bits : List Bool) : numeral bits < 2^bits.length := by
  induction bits with
  | nil => decide
  | cons b bits ih =>
    simp only [numeral,List.length_cons,pow_succ]
    cases b
    · change 0+2*numeral bits<2^bits.length*2;omega
    · change 1+2*numeral bits<2^bits.length*2;omega
private theorem decodeFin_numeral (width : Nat) (bits : List Bool) (len : bits.length=width) :
    decodeFin width bits=some ⟨numeral bits,by rw [←len];exact numeral_lt bits⟩ := by
  induction width generalizing bits with
  | zero =>
    cases bits with
    | nil => rfl
    | cons b bits => simp only [List.length_cons] at len;omega
  | succ width ih =>
    cases bits with
    | nil => simp only [List.length_nil] at len;omega
    | cons b bits =>
      have length : bits.length=width := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using len
      rw [decodeFin,ih bits length]
      rfl
private theorem accumulate_ge (a : Nat) (bits : List Bool) : a≤accumulate a bits := by
  induction bits generalizing a with
  | nil => exact le_rfl
  | cons b bits ih =>
    have h:=ih (2*a+digit b)
    change a≤accumulate (2*a+digit b) bits
    omega
private theorem cap_is_sound (a n : Nat) (bits : List Bool) (cap : n≤a) : n≤accumulate a bits :=
  le_trans cap (accumulate_ge a bits)
private theorem decode_input_exact {n width : Nat} (fuel : Nat) (payload tail : List Bool)
    (len : payload.length=width) :
    decodeCircuitTreeAtDepth n width (fuel+1) (false::false::false::(payload++tail))=
      if h : numeral payload < n then some (CircuitTree.input ⟨numeral payload,h⟩,tail) else none := by
  rw [decodeCircuitTreeAtDepth]
  have enough : ¬(payload++tail).length < width := by simp only [List.length_append];omega
  rw [dif_neg enough,List.take_append_of_le_length (by omega),←len,List.take_length]
  dsimp only
  rw [decodeFin_numeral payload.length payload rfl,List.drop_left]
end FullBodyClosure
