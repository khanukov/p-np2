import NormalClockClosure.Target
namespace NormalClockClosure
open Pnp3.Complexity.Uniform.V1
private theorem succ_le_two_pow (q : Nat) : q+1 ≤ 2^q := by
  induction q with
  | zero=>decide
  | succ q ih=>rw [Nat.pow_succ];omega
private theorem deadline_bound (k N : Nat) :
    17592186044416*(k+1)*(N+1)^8 ≤ polyClock (degree k) N := by
  by_cases zero:N=0
  · subst N
    have cpos:degree k≠0:=by unfold degree;omega
    simp only [Nat.zero_add,Nat.one_pow,Nat.mul_one,polyClock,zero_pow cpos,Nat.zero_add]
    unfold degree
    omega
  by_cases one:N=1
  · subst N
    simp only [polyClock,one_pow]
    change 17592186044416*(k+1)*256 ≤ 1+(4503599627370496*(k+1)+64)
    omega
  have two:2 ≤ N:=by omega
  have p:(N+1)^8 ≤ (2*N)^8:=Nat.pow_le_pow_left (by omega) 8
  have c8:8 ≤ degree k:=by unfold degree;omega
  have coef:17592186044416*(k+1)*256 ≤ degree k-8+1:=by unfold degree;omega
  have factor:17592186044416*(k+1)*256 ≤ N^(degree k-8):=
    coef.trans ((succ_le_two_pow _).trans (Nat.pow_le_pow_left two _))
  calc
    17592186044416*(k+1)*(N+1)^8 ≤ 17592186044416*(k+1)*(2*N)^8:=Nat.mul_le_mul_left _ p
    _ = (17592186044416*(k+1)*256)*N^8:=by ring
    _ ≤ N^(degree k-8)*N^8:=Nat.mul_le_mul_right _ factor
    _ = N^(degree k):=by rw [←Nat.pow_add,Nat.sub_add_cancel c8]
    _ ≤ polyClock (degree k) N:=Nat.le_add_right _ _
/-- Both original allocation and the published NORMAL phase deadline are
absorbed for every N, including 0 and 1, by this explicit fixed-k V1 clock. -/
theorem clock_bound (k N : Nat) :
    RawCallerClosure.allocation k N ≤ polyClock (degree k) N ∧
    17592186044416*(k+1)*(N+1)^8 ≤ polyClock (degree k) N := by
  have gd:RawCallerClosure.allocation k N ≤ 17592186044416*(k+1)*(N+1)^8:=by
    change 1099511627776*(k+1)*(N+1)^8 ≤ 17592186044416*(k+1)*(N+1)^8
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  exact ⟨gd.trans (deadline_bound k N),deadline_bound k N⟩
theorem clock_bound_mirror (k N : Nat) :
    1099511627776*(k+1)*(N+1)^8 ≤
      N^(4503599627370496*(k+1)+64)+(4503599627370496*(k+1)+64) ∧
    17592186044416*(k+1)*(N+1)^8 ≤
      N^(4503599627370496*(k+1)+64)+(4503599627370496*(k+1)+64) := clock_bound k N
#print axioms clock_bound
#print axioms clock_bound_mirror
private theorem caller_price (R Q initial elapsed : Nat)
    (qb:Q ≤ 3*R+2) (ip:initial ≤ 4096*(R+1)^2)
    (ep:elapsed ≤ Q*(2147483648*(R+1)^6)) :
    initial+elapsed ≤ 17179869184*(R+1)^7 := by
  have pp:(R+1)^2 ≤ (R+1)^7:=Nat.pow_le_pow_right (by omega) (by decide)
  have i:initial ≤ 4096*(R+1)^7:=ip.trans (Nat.mul_le_mul_left _ pp)
  have q:Q ≤ 4*(R+1):=by omega
  have e:elapsed ≤ 8589934592*(R+1)^7:=by
    calc elapsed ≤ Q*(2147483648*(R+1)^6):=ep
         _ ≤ (4*(R+1))*(2147483648*(R+1)^6):=Nat.mul_le_mul_right _ q
         _ = 8589934592*(R+1)^7:=by ring
  omega
private theorem front_price (k N pre elapsed : Nat)
    (pp:pre ≤ 137438953472*(k+1)*(N+1)^6)
    (ep:elapsed ≤ 17179869184*(N+1)^7) :
    pre+elapsed ≤ 274877906944*(k+1)*(N+1)^7 := by
  have pow:(N+1)^6 ≤ (N+1)^7:=Nat.pow_le_pow_right (by omega) (by decide)
  have p:pre ≤ 137438953472*(k+1)*(N+1)^7:=pp.trans (Nat.mul_le_mul_left _ pow)
  have e:elapsed ≤ 17179869184*(k+1)*(N+1)^7:=ep.trans (Nat.mul_le_mul_right _ (by omega))
  calc pre+elapsed ≤ 137438953472*(k+1)*(N+1)^7+17179869184*(k+1)*(N+1)^7:=Nat.add_le_add p e
       _ = 154618822656*((k+1)*(N+1)^7):=by ring
       _ ≤ 274877906944*((k+1)*(N+1)^7):=Nat.mul_le_mul_right _ (by decide)
       _ = _:=by ring
private theorem normal_price (k N r P d u : Nat) (rn:r ≤ N) (pn:P+1 ≤ 64*(N+1))
    (dp:d ≤ 274877906944*(k+1)*(N+1)^7)
    (up:u ≤ 1048576*(r+1)^4*(P+1)^2) :
    d+u ≤ 549755813888*(k+1)*(N+1)^7 := by
  have rpow:(r+1)^4 ≤ (N+1)^4:=Nat.pow_le_pow_left (by omega) 4
  have ppow:(P+1)^2 ≤ (64*(N+1))^2:=Nat.pow_le_pow_left pn 2
  have coarse:u ≤ 4294967296*(N+1)^6:=by
    calc u ≤ 1048576*(r+1)^4*(P+1)^2:=up
         _ ≤ 1048576*(N+1)^4*(64*(N+1))^2:=Nat.mul_le_mul (Nat.mul_le_mul_left _ rpow) ppow
         _ = 4294967296*(N+1)^6:=by ring
  have pow:(N+1)^6 ≤ (N+1)^7:=Nat.pow_le_pow_right (by omega) (by decide)
  have up':u ≤ 4294967296*(k+1)*(N+1)^7:=coarse.trans (Nat.mul_le_mul (by omega) pow)
  calc d+u ≤ 274877906944*(k+1)*(N+1)^7+4294967296*(k+1)*(N+1)^7:=Nat.add_le_add dp up'
       _ = 279172874240*((k+1)*(N+1)^7):=by ring
       _ ≤ 549755813888*((k+1)*(N+1)^7):=Nat.mul_le_mul_right _ (by decide)
       _ = _:=by ring
private theorem source_room_price (k N t : Nat) (p:t ≤ 549755813888*(k+1)*(N+1)^7) :
    t+1 ≤ RawCallerClosure.allocation k N := by
  have pow:(N+1)^7 ≤ (N+1)^8:=Nat.pow_le_pow_right (by omega) (by decide)
  have unit:1 ≤ (k+1)*(N+1)^7:=Nat.succ_le_of_lt (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
  have mono:(k+1)*(N+1)^7 ≤ (k+1)*(N+1)^8:=Nat.mul_le_mul_left _ pow
  have pt:t ≤ 549755813888*((k+1)*(N+1)^7):=by simpa only [Nat.mul_assoc] using p
  change t+1 ≤ 1099511627776*(k+1)*(N+1)^8
  calc t+1 ≤ 549755813889*((k+1)*(N+1)^7):=by omega
       _ ≤ 1099511627776*((k+1)*(N+1)^8):=Nat.mul_le_mul (by decide) mono
       _ = _:=by ring
end NormalClockClosure
