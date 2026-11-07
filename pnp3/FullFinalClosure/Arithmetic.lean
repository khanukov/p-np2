import FullFinalClosure.Target
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
private theorem allocation_part (k N : Nat) :
    VirtualFinalClosure.allocation k N ≤ 281474976710656*((k+1)^8*(N+1)^(4*k+24)) := by
  have kp:(k+1)^4≤(k+1)^8:=Nat.pow_le_pow_right (by omega) (by decide)
  have np:(N+1)^(k+12)≤(N+1)^(4*k+24):=Nat.pow_le_pow_right (by omega) (by omega)
  unfold VirtualFinalClosure.allocation
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul kp np)
private theorem normal_part (k N : Nat) :
    17592186044416*(k+1)*(N+1)^8 ≤ 17592186044416*((k+1)^8*(N+1)^(4*k+24)) := by
  have kp:k+1≤(k+1)^8:=by simpa only [pow_one] using Nat.pow_le_pow_right (show 0<k+1 by omega) (show 1≤8 by decide)
  have np:(N+1)^8≤(N+1)^(4*k+24):=Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul kp np)
private theorem coarse_sum (U a b d : Nat) (one:1≤U)
    (ap:a≤281474976710656*U) (bp:b≤17592186044416*U) (de:d=18446744073709551616*U) :
    a+(d+b+1)+1 ≤ 73786976294838206464*U := by omega
private theorem coarse_allocation (k N : Nat) :
    allocation k N ≤ 73786976294838206464*(k+1)^8*(N+1)^(4*k+24) := by
  have bound:=coarse_sum ((k+1)^8*(N+1)^(4*k+24)) (VirtualFinalClosure.allocation k N)
    (17592186044416*(k+1)*(N+1)^8) (VirtualFinalClosure.deadline k N)
    (Nat.succ_le_of_lt (by positivity)) (allocation_part k N) (normal_part k N)
    (by unfold VirtualFinalClosure.deadline;rw [Nat.mul_assoc])
  unfold allocation runtimeBound
  conv_rhs=>rw [Nat.mul_assoc]
  exact bound
private theorem succ_le_two_pow (q : Nat) : q+1 ≤ 2^q := by
  induction q with
  | zero=>decide
  | succ q ih=>rw [Nat.pow_succ];omega
private theorem polynomial_majorant (C d c : Nat) (pos:0<c)
    (zero:C≤c) (degreeBound:d≤c) (coefficient:C*2^d≤c-d+1) (N : Nat) :
    C*(N+1)^d ≤ polyClock c N := by
  by_cases z:N=0
  · subst N
    simpa only [Nat.zero_add,Nat.one_pow,Nat.mul_one,polyClock,zero_pow (by omega : c≠0),Nat.zero_add] using zero
  by_cases o:N=1
  · subst N
    simp only [polyClock,one_pow,show (1:Nat)+1=2 from rfl]
    omega
  have two:2≤N:=by omega
  have p:(N+1)^d≤(2*N)^d:=Nat.pow_le_pow_left (by omega) d
  have factor:C*2^d≤N^(c-d):=coefficient.trans ((succ_le_two_pow _).trans (Nat.pow_le_pow_left two _))
  calc
    C*(N+1)^d ≤ C*(2*N)^d:=Nat.mul_le_mul_left _ p
    _ = (C*2^d)*N^d:=by rw [Nat.mul_pow];ac_rfl
    _ ≤ N^(c-d)*N^d:=Nat.mul_le_mul_right _ factor
    _ = N^c:=by rw [←Nat.pow_add,Nat.sub_add_cancel degreeBound]
    _ ≤ polyClock c N:=Nat.le_add_right _ _
private theorem power66 : (2:Nat)^66=73786976294838206464 := by norm_num
private theorem coefficient_bound (k : Nat) :
    (73786976294838206464*(k+1)^8)*2^(4*k+24) ≤ 2^(4*k+128)*(k+1)^8 := by
  rw [←power66]
  calc ((2:Nat)^66*(k+1)^8)*2^(4*k+24) = 2^(66+(4*k+24))*(k+1)^8:=by
         rw [Nat.pow_add (2:Nat) 66 (4*k+24)]
         exact Nat.mul_right_comm _ _ _
       _ ≤ 2^(4*k+128)*(k+1)^8:=Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
private theorem zero_coefficient (k : Nat) :
    73786976294838206464*(k+1)^8 ≤ 2^(4*k+128)*(k+1)^8 := by
  rw [←power66]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
private theorem clock_allocation (k N : Nat) : allocation k N ≤ polyClock (degree k) N := by
  have small:=zero_coefficient k
  have coeff:=coefficient_bound k
  have pos:0<degree k:=by unfold degree;omega
  have zero:73786976294838206464*(k+1)^8≤degree k:=by unfold degree;omega
  have degreeBound:4*k+24≤degree k:=by unfold degree;omega
  have coefficient:(73786976294838206464*(k+1)^8)*2^(4*k+24)≤degree k-(4*k+24)+1:=by unfold degree;omega
  exact (coarse_allocation k N).trans (polynomial_majorant _ _ _ pos zero degreeBound coefficient N)
private theorem old_allocation (k N : Nat) :
    RawCallerClosure.allocation k N ≤ VirtualFinalClosure.allocation k N := by
  have kp:k+1≤(k+1)^4:=by simpa only [pow_one] using Nat.pow_le_pow_right (show 0<k+1 by omega) (show 1≤4 by decide)
  have np:(N+1)^8≤(N+1)^(k+12):=Nat.pow_le_pow_right (by omega) (by omega)
  change 1099511627776*(k+1)*(N+1)^8≤281474976710656*(k+1)^4*(N+1)^(k+12)
  exact Nat.mul_le_mul (Nat.mul_le_mul (by decide) kp) np
private theorem a_room (k N : Nat) :
    VirtualFinalClosure.spaceBound k N+1 < tapeLength N (VirtualFinalClosure.allocation k N) := by
  let U:=(k+1)^2*(N+1)^(k+3)
  have one:1≤U:=Nat.succ_le_of_lt (by dsimp only [U];positivity)
  have kp:(k+1)^2≤(k+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have np:(N+1)^(k+3)≤(N+1)^(k+12):=Nat.pow_le_pow_right (by omega) (by omega)
  have large:281474976710656*U≤VirtualFinalClosure.allocation k N:=
    by simpa only [U,VirtualFinalClosure.allocation,Nat.mul_assoc] using Nat.mul_le_mul (Nat.mul_le_mul_left 281474976710656 kp) np
  have space:VirtualFinalClosure.spaceBound k N=1048576*U:=by
    unfold VirtualFinalClosure.spaceBound
    dsimp only [U]
    ac_rfl
  rw [space]
  unfold tapeLength
  omega
end FullFinalClosure
