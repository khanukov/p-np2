import CanonicalLeaf.Body
namespace CanonicalLeaf
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 10000
private theorem digit_value (bs : List Bool) (j : Nat) (hj : j<bs.length) :
    bs[j]! =Nat.testBit (Body.value bs) j := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b bs ih =>
    have bit (i : Nat) : Nat.testBit (Body.value (b::bs)) i=
        if i<1 then Nat.testBit b.toNat i else Nat.testBit (Body.value bs) (i-1) := by
      change Nat.testBit (b.toNat+2*Body.value bs) i=_
      simpa only [Nat.pow_one,Nat.add_comm] using
        Nat.testBit_two_pow_mul_add (Body.value bs) (b:=b.toNat) (i:=1) (by cases b <;> decide) i
    cases j with
    | zero => change b=Nat.testBit (Body.value (b::bs)) 0; rw [bit,if_pos (by decide : 0<1)]; cases b <;> decide
    | succ j => rw [bit]; simpa using ih j (by simpa using hj)
private theorem iter_value_mod (bs : List Bool) (r : Nat) :
    Body.value (Body.iterBits bs r)=(Body.value bs+r)%2^bs.length := by
  induction r generalizing bs with
  | zero => simpa only [Body.iterBits,Nat.add_zero] using (Nat.mod_eq_of_lt (Body.value_lt bs)).symm
  | succ r ih =>
    change Body.value (Body.iterBits (Body.inc bs).1 r)=(Body.value bs+(r+1))%2^bs.length
    rw [ih,Body.inc_length]
    have hm : Body.value (Body.inc bs).1%2^bs.length=(Body.value bs+1)%2^bs.length := by
      rw [←Body.inc_value bs,Nat.add_mod]; cases (Body.inc bs).2 <;> simp
    calc
      _=(Body.value (Body.inc bs).1%2^bs.length+r)%2^bs.length := by simp [Nat.add_mod]
      _=((Body.value bs+1)%2^bs.length+r)%2^bs.length := by rw [hm]
      _=_ := by simp [Nat.add_mod,Nat.add_comm,Nat.add_left_comm]
private theorem iter_digit (n r j : Nat) (hr : r<2^n) (hj : j<n) :
    (Body.iterBits (List.replicate n false) r)[j]! =Nat.testBit r j := by
  rw [digit_value _ j (by simpa only [Body.iter_length,List.length_replicate] using hj),
    iter_value_mod,Body.zero_value,Nat.zero_add,List.length_replicate,Nat.mod_eq_of_lt hr]
/-- Actual Stream counter image agrees with the original Core vector, without reversing beta. -/
theorem counter_frame (U : Nat → Option Bool) (S z n A r marks : Nat) (lift : Bool) (hr : r<2^n) :
    ∀ j : Fin n, Stream.Target.image U S z n A r marks lift (S+z+n+3-1-j.val)=
      some (Pnp3.Core.vecOfNat n r j) := by
  intro j
  have hit : S+z+2<S+z+n+3-1-j.val ∧ S+z+n+3-1-j.val<S+z+2+n+1 := by omega
  dsimp only [Stream.Target.image]
  rw [if_pos hit]
  have index : S+z+2+n+1-1-(S+z+n+3-1-j.val)=j.val := by omega
  rw [index,iter_digit n r j.val hr j.isLt]; rfl
/-- Prepared counter-frame execution only; not a new raw paid-row orbit theorem. -/
theorem counter_leaf (k N B S z n A r marks : Nat) (lift : Bool) (U : Nat → Option Bool)
    (hr : r<2^n) (fit : S+z+n+3<tapeLength N B)
    (sep : Stream.Target.image U S z n A r marks lift (S+z+2)=none)
    (last : Stream.Target.image U S z n A r marks lift (S+z+n+3)=none) :
    let T : Fin (tapeLength N B) → Option Bool:=fun i => Stream.Target.image U S z n A r marks lift i.val
    let H : Fin (tapeLength N B):=⟨S+z+n+3,fit⟩
    let value:=if 0<n then Nat.testBit r 0 else false
    (machine k).run 5 ⟨entry k,H,T⟩=
      ⟨if n=0 then (machine k).reject else result k value,H,
        if n=0 then T else Function.update T H (some value)⟩ := by
  have eq : S+z+2+n+1=S+z+n+3 := by omega
  have proof:=prepared k (S+z+2) n (Pnp3.Core.vecOfNat n r)
    (fun i : Fin (tapeLength N B) => Stream.Target.image U S z n A r marks lift i.val)
    (by rw [eq]; exact fit) sep (by simpa only [eq] using last)
    (by intro j; simpa only [eq] using counter_frame U S z n A r marks lift hr j)
  simpa only [eq] using proof.1
end CanonicalLeaf
