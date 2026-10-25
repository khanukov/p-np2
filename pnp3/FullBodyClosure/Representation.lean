import FullBodyClosure.Run
import SerializedPositiveBody.Driver
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
/-- Proof-only record decoding; physical records are three occupied tape cells. -/
private def recordBit (c : Fin 7) (i : Nat) : Bool :=
  match i with | 0 => decide (4 ≤ c.val) | 1 => decide (2 ≤ c.val%4) | _ => decide (c.val%2=1)
private def stackBits (K : List (Fin 7)) (i : Nat) : Bool :=
  match K[i/3]? with | some c => recordBit c (i%3) | none => true
private theorem record_not_free (c : Fin 7) : (recordBit c 0 && recordBit c 1 && recordBit c 2)=false := by
  fin_cases c <;> decide
private theorem stackBits_record (K : List (Fin 7)) (j : Nat) (c : Fin 7) (h : K[j]?=some c) (b : Nat) (hb : b < 3) :
    stackBits K (3*j+b)=recordBit c b := by
  simp only [stackBits,show (3*j+b)/3=j by omega,h,show (3*j+b)%3=b by omega]
private theorem stackBits_free (K : List (Fin 7)) (j : Nat) (h : K.length≤j) (b : Nat) (hb : b < 3) :
    stackBits K (3*j+b)=true := by
  rw [stackBits,show (3*j+b)/3=j by omega,List.getElem?_eq_none (by omega)]
/-- Shared ghost memory image. Each varying counter is physically unary on the tape. -/
private def arena (T : Nat → Option Bool) (D : Nat → Nat) (g v : Nat) (K : List (Fin 7)) : Nat → Option Bool :=
  fun i=>if D 5 < i ∧ i < D 6 then some (decide (i-D 5≤v)) else
    if D 6 < i ∧ i < D 7 then some (decide (i-D 6≤g-v)) else
    if D 10 < i ∧ i < D 11 then some (stackBits K (i-D 10-1)) else T i
private def memory (T : Nat → Option Bool) (D : Nat → Nat) (S M W u : Nat) : Nat → Option Bool :=
  fun i=>if i=M+u ∧ i < S then none else
    if D 4 < i ∧ i < D 5 then some (decide (i-D 4≤W-u)) else
    if D 11 < i ∧ i < D 12 then some (decide (i-D 11≤u)) else T i
private def RepTape (T : Nat → Option Bool) (D : Nat → Nat) (S M g W u v : Nat) (K : List (Fin 7)) : Nat → Option Bool :=
  memory (arena T D g v K) D S M W u
private theorem outside_field (D : Nat → Nat)
    (mono : ∀ a b,a≤b → b≤12 → D a≤D b) {j k i : Nat}
    (hj : j < 12) (hk : k < 12) (ne : j≠k) (inside : D j < i ∧ i < D (j+1)) :
    ¬(D k < i ∧ i < D (k+1)) := by
  by_cases h : j < k
  · have :=mono (j+1) k (by omega) (by omega);omega
  · have :=mono (k+1) j (by omega) (by omega);omega
private theorem memory_below {T D S M W u i}
    (mono : ∀ a b,a≤b → b≤12 → D a≤D b) (low : i < D 0) :
    memory T D S M W u i=(if i=M+u ∧ i < S then none else T i) := by
  have a:=mono 0 4 (by decide) (by decide)
  have b:=mono 0 11 (by decide) (by decide)
  simp only [memory,if_neg (show ¬(D 4 < i ∧ i < D 5) from by omega),
    if_neg (show ¬(D 11 < i ∧ i < D 12) from by omega)]
private theorem arena_below {T D g v K i}
    (mono : ∀ a b,a≤b → b≤12 → D a≤D b) (low : i < D 0) :
    arena T D g v K i=T i := by
  have a:=mono 0 5 (by decide) (by decide)
  have b:=mono 0 6 (by decide) (by decide)
  have c:=mono 0 10 (by decide) (by decide)
  simp only [arena,if_neg (show ¬(D 5 < i ∧ i < D 6) from by omega),
    if_neg (show ¬(D 6 < i ∧ i < D 7) from by omega),if_neg (show ¬(D 10 < i ∧ i < D 11) from by omega)]
private theorem RepTape_below {T D S M g W u v K i}
    (mono : ∀ a b,a≤b → b≤12 → D a≤D b) (low : i < D 0) :
    RepTape T D S M g W u v K i=(if i=M+u ∧ i < S then none else T i) := by
  rw [RepTape,memory_below mono low,arena_below mono low]
/-- Pointwise update commuting with the live source view; useful for every native consumer. -/
private theorem memory_patch (T : Nat → Option Bool) (D : Nat → Nat) (S M W u h : Nat) (b : Option Bool)
    (after : S≤h) (not4 : ¬(D 4 < h ∧ h < D 5)) (not11 : ¬(D 11 < h ∧ h < D 12)) :
    (fun i=>if i=h then b else memory T D S M W u i)=
      memory (fun i=>if i=h then b else T i) D S M W u := by
  funext i
  by_cases eq : i=h
  · subst i
    rw [if_pos rfl]
    simp only [memory,if_neg (show ¬(h=M+u ∧ h < S) from by omega),
      if_neg not4,if_neg not11,ite_true]
  · simp only [memory,if_neg eq]
end FullBodyClosure
