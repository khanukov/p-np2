import PhysicalCallerClosure.AssignmentRows
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
private theorem value_ofFn : ∀ n (beta : Fin n → Bool),
    Body.value (List.ofFn beta)=Pnp3.Models.bitVecToNat beta := by
  intro n
  induction n with
  | zero => intro beta;simp [Body.value,Pnp3.Models.bitVecToNat]
  | succ n ih =>
    intro beta
    rw [List.ofFn_succ,Body.value,Pnp3.Models.bitVecToNat_succ,←ih]
    congr 1
    have eq:(0:Fin (n+1))=⟨0,by omega⟩:=by apply Fin.ext;simp
    rw [eq]
    cases beta ⟨0,by omega⟩ <;> rfl
private theorem reify (bs : List Bool) : (List.ofFn fun j:Fin bs.length=>bs[j.val]!)=bs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_ofFn]
    exact getElem!_pos bs i hi'
private theorem beta_of_value (bs : List Bool) :
    Pnp3.Core.vecOfNat bs.length (Body.value bs)=(fun j:Fin bs.length=>bs[j.val]!) := by
  have val:=value_ofFn bs.length (fun j:Fin bs.length=>bs[j.val]!)
  rw [reify] at val
  rw [val]
  exact Pnp3.Models.vecOfNat_bitVecToNat _
private theorem initial_value (n row : Nat) (hr:row < 2^n) :
    Body.value (List.ofFn (Pnp3.Core.vecOfNat n row))=row := by
  rw [value_ofFn]
  exact Pnp3.Models.bitVecToNat_vecOfNat hr
private theorem canonical_increment (n row : Nat) (hr:row < 2^n) :
    let bs:=List.ofFn (Pnp3.Core.vecOfNat n row)
    (Body.inc bs).2=decide (row+1=2^n) ∧
      ∀ j:Fin n,(Body.inc bs).1[j.val]! =Pnp3.Core.vecOfNat n ((row+1)%(2^n)) j := by
  dsimp only
  let bs:=List.ofFn (Pnp3.Core.vecOfNat n row)
  let next:=(Body.inc bs).1
  have len:bs.length=n:=List.length_ofFn
  have ln:next.length=n:=by dsimp only [next];rw [Body.inc_length,len]
  have val:=Body.inc_value bs
  rw [initial_value n row hr,len] at val
  have small:=Body.value_lt next
  rw [ln] at small
  have overflow:(Body.inc bs).2=decide (row+1=2^n) ∧ Body.value next=(row+1)%(2^n):=by
    cases h:(Body.inc bs).2 with
    | false =>
      simp only [h] at val
      have before:row+1 < 2^n:=by change Body.value next=row+1 at val;omega
      refine ⟨?_,?_⟩
      · simp only [decide_eq_false (show row+1≠2^n by omega)]
      · rw [Nat.mod_eq_of_lt before];exact val
    | true =>
      simp only [h,if_true] at val
      have last:row+1=2^n:=by omega
      have zero:Body.value next=0:=by change Body.value next+2^n=row+1 at val;omega
      refine ⟨?_,?_⟩
      · simp only [last,decide_true]
      · rw [last,Nat.mod_self];exact zero
  refine ⟨overflow.1,?_⟩
  intro j
  let j':Fin next.length:=⟨j.val,by rw [ln];exact j.isLt⟩
  have eq:=congrFun (beta_of_value next) j'
  change Nat.testBit (Body.value next) j.val=next[j.val]! at eq
  rw [overflow.2] at eq
  exact eq.symm
end PhysicalCallerClosure
